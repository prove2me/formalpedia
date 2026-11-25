-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_eq_zero_of_two_rankOne_744d0b65b8a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:49.379703+00:00
-- url     : https://prove2.me/submissions/76e1405a-eebf-4fbd-af70-bca51a3af183

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_det_eq_zero_of_rows_smul_c90b5b458b1e
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_polCoef
import Theorems.Thm_ReciprocityTheory_AnForm_A_polCoef_eq_zero


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ)
    {a b : Fin D} (hab : a ≠ b) (x x' : Fin D → ℂ) (ha : A a = vecMulVec x w)
    (hb : A b = vecMulVec x' w) : mdisc A = 0 := by
  rw [mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨i, hi⟩ := hr a
    obtain ⟨j, hj⟩ := hr b
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    refine mul_eq_zero_of_right _ (det_eq_zero_of_rows_smul _ w hij (x i) (x' j) ?_ ?_)
    · funext k; simp [hi, ha, vecMulVec_apply]
    · funext k; simp [hj, hb, vecMulVec_apply]
  · rw [polCoef_eq_zero r hr, zero_mul]
end GroundTheory.Heights₂.Heights.MaDensLogPow
