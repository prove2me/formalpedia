-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_eq_prod_04df03d762f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:12.410976+00:00
-- url     : https://prove2.me/submissions/2fe8abd4-08ff-4920-b69c-7a818d50cb82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Complex Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (z : σ → ℂ)
    (Z : Multiset ℂ) (hZ : Multiset.card Z = d)
    (hc : ∀ j : Fin d, c j z = (-1) ^ (d - (j : ℕ)) * Z.esymm (d - (j : ℕ))) (t : ℂ) :
    weierstrassPolynomial c (pointWithLast z t) = (Z.map fun a => t - a).prod := by
  subst hZ
  set p : Polynomial ℂ := (Z.map fun a => Polynomial.X - Polynomial.C a).prod with hp
  have hdeg : p.natDegree = Multiset.card Z := Polynomial.natDegree_multiset_prod_X_sub_C_eq_card Z
  have h1 : p.eval t = (Z.map fun a => t - a).prod := by
    rw [hp, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun a _ => by simp
  rw [← h1, Polynomial.eval_eq_sum_range' (n := Multiset.card Z + 1) (by omega), Finset.sum_range_succ,
    hp, Multiset.prod_X_sub_C_coeff Z le_rfl, ← hp]
  simp only [weierstrassPolynomial, Nat.sub_self, pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left,
    Multiset.map_singleton, Multiset.prod_zero, Multiset.sum_singleton, one_mul]
  rw [add_comm]
  congr 1
  simp only [show (fun i => pointWithLast z t (some i)) = z from rfl, show pointWithLast z t none = t from rfl, hc]
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1) ^ (Multiset.card Z - i) * Z.esymm (Multiset.card Z - i) * t ^ i)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hp, Multiset.prod_X_sub_C_coeff Z (Finset.mem_range.1 hi).le]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
