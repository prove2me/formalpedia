-- Prove2me | solution 1 for ThreeSum.LightTernaryBudgetStep.changed_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:26.130203+00:00
-- url     : https://prove2.me/submissions/59c02805-e1f4-4d1f-b33a-2b4a3692ab09

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBudgetStep
open Light
set_option maxHeartbeats 3000000
namespace ThreeSum.LightTernaryBudgetStep
theorem _root_.solution (μ : ℕ→ ℤ) (base p a b s xB xC xP tB tC tP : ℕ) :
    Seg (changed μ base p a b s xB xC xP tB tC tP) base
      (nextValues p a b s xB xC xP tB tC tP) := by
  intro i hi
  simp only [nextValues,List.length_cons,List.length_nil] at hi
  have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [changed,nextValues]
end ThreeSum.LightTernaryBudgetStep
