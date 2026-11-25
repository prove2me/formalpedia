-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_det_eq_zero_of_rows_smul_c90b5b458b1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:35.0697+00:00
-- url     : https://prove2.me/submissions/6d730bd6-5cd4-4b03-a9a5-f86bddaa7525

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow

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
theorem _root_.solution (M : Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ) {i j : Fin D}
    (hij : i ≠ j) (a b : ℂ) (hi : M i = a • w) (hj : M j = b • w) : M.det = 0 := by
  by_cases ha : a = 0
  · exact Matrix.det_eq_zero_of_row_eq_zero i fun k => by simp [hi, ha]
  · rw [← Matrix.det_updateRow_add_smul_self M hij.symm (-(b / a))]
    refine Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [updateRow_self, hi, hj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
end GroundTheory.Heights₂.Heights.MaDensLogPow
