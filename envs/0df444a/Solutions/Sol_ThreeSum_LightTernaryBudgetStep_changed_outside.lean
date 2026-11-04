-- Prove2me | solution 1 for ThreeSum.LightTernaryBudgetStep.changed_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:52.49077+00:00
-- url     : https://prove2.me/submissions/a3a4bf8d-7ee5-4d56-a797-1abce49511d3

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
    SameOutside μ (changed μ base p a b s xB xC xP tB tC tP) base 6 := by
  intro i hi
  have h0 : i≠base := by omega
  have h1 : i≠base+1 := by omega
  have h2 : i≠base+2 := by omega
  have h3 : i≠base+3 := by omega
  have h4 : i≠base+4 := by omega
  have h5 : i≠base+5 := by omega
  simp [changed,Function.update_of_ne,h0,h1,h2,h3,h4,h5]
end ThreeSum.LightTernaryBudgetStep
