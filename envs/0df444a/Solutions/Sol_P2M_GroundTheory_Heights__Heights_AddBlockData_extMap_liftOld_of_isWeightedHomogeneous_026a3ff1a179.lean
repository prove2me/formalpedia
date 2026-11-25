-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:48.865806+00:00
-- url     : https://prove2.me/submissions/30d9eabc-d2d3-434e-bcd1-7e77977743d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_comp_liftOld_b676d46bc421
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_eval_Hom_monomial_blockVal_2e069a232866

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    D.extMap (D.liftOld f) = C (P.mkF f) * ∏ k, X (some k) ^ δ k := by
  have h : D.extMap (D.liftOld f) = eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
      (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) f := by
    rw [← D.extMap_comp_liftOld]
    rfl
  rw [h]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [eval₂Hom_monomial_blockVal, hf (mem_support_iff.mp hd)]
end GroundTheory.Heights₂.Heights.AddBlockData
