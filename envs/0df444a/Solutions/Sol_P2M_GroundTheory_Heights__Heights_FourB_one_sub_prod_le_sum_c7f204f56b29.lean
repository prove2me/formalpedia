-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_one_sub_prod_le_sum_c7f204f56b29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:18.470846+00:00
-- url     : https://prove2.me/submissions/28d4590f-1d8c-414c-b7e3-98a5ce6e44e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PDegreeRatio
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {ι : Type*} (s : Finset ι) (g h : ι → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) (hgh : ∀ i, 1 - g i ≤ h i) :
    1 - ∏ i ∈ s, g i ≤ ∑ i ∈ s, h i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i _ => hg0 i
    have hP1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one (fun i _ => hg0 i) fun i _ => hg1 i
    have key : 1 - g a * ∏ i ∈ s, g i = (1 - ∏ i ∈ s, g i) + (1 - g a) * ∏ i ∈ s, g i := by ring
    have h1 : (1 - g a) * ∏ i ∈ s, g i ≤ 1 - g a :=
      mul_le_of_le_one_right (by linarith [hg1 a]) hP1
    linarith [hgh a]
end GroundTheory.Heights₂.Heights.FourB
