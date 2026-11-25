-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_differentiableAt_coeff_prod_974a041f6356
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:01.774916+00:00
-- url     : https://prove2.me/submissions/8f55bae8-15c8-4867-beb0-9a718b53c091

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor

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
open Polynomial Filter Topology Classical
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Multiset ℂ)
    (g : ℂ → E → ℂ) (x : E) (hg : ∀ τ, DifferentiableAt ℂ (g τ) x) :
    ∀ k : ℕ, DifferentiableAt ℂ (fun s => ((F.map fun τ => X - C (g τ s)).prod).coeff k) x := by
  induction F using Multiset.induction_on with
  | empty => intro k; simp
  | cons σ F ih =>
    intro k
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    cases k with
    | zero =>
      simp only [coeff_X_mul_zero, zero_sub]
      exact ((hg σ).mul (ih 0)).neg
    | succ n =>
      simp only [coeff_X_mul]
      exact (ih n).sub ((hg σ).mul (ih (n + 1)))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
