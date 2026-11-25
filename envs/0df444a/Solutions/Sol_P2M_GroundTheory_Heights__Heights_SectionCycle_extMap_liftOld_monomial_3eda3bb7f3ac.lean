-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_monomial_3eda3bb7f3ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:33.303739+00:00
-- url     : https://prove2.me/submissions/e87b80b4-96ae-4375-845a-c7c4b3e31dc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_prod_pow_weight_2b5afadbd0cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_oldCoord_injective_8ba726ea0c16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (s : Coord n →₀ ℕ) (a : ℤ) :
    D.extMap (D.liftOld (monomial s a)) =
      C (P.mkF (monomial s a)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) s k) := by
  rw [prod_pow_weight (fun k ↦ (X (some k) : MvPolynomial (Option ι) P.FunField))]
  rw [AddBlockData.liftOld, rename_monomial, AddBlockData.extMap, coe_eval₂Hom, eval₂_monomial,
    Finsupp.prod_mapDomain_index_inj (oldCoord_injective D)]
  rw [monomial_eq, map_mul, map_finsuppProd, map_mul, map_finsuppProd]
  simp only [map_pow, mul_pow, Finsupp.prod_mul]
  have ha : C (P.mkF (C a)) = (Int.castRingHom (MvPolynomial (Option ι) P.FunField)) a := by
    rw [← RingHom.comp_apply P.mkF C, eq_intCast, map_intCast, eq_intCast]
  rw [ha, mul_assoc]
  rfl
end GroundTheory.Heights₂.Heights.SectionCycle
