-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLeviForm_levi_sum_nonneg_cfff48a7513c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:16.391958+00:00
-- url     : https://prove2.me/submissions/b63760fe-77c4-43a3-8af9-ca63ece2cf9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsLineLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.FubiniStudyLeviForm
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FubiniStudyLeviForm
theorem _root_.solution {K : Type} {z : ι → ℂ} (f : K → (ι → ℂ) → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ ReciprocityTheory.AnForm.levi (f k) z w)
    (w : ι → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, f k y) z ∧
      0 ≤ ReciprocityTheory.AnForm.levi (fun y => ∑ k ∈ s, f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [ReciprocityTheory.AnForm.levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, f k y) =
        fun y => (fun y' => ∑ k ∈ s, f k y') y + 1 * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y' => ∑ k ∈ s, f k y') (g := f a) 1 ih.1 (hf a) w]
    have h1 := hl a w
    have h2 := ih.2
    linarith
end GroundTheory.Heights₂.Heights.FubiniStudyLeviForm
