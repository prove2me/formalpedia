-- Prove2me | solution 1 for ThreeSum.LightTernaryBudgetStep.nextValues_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:27.644193+00:00
-- url     : https://prove2.me/submissions/c04c6df4-7960-4a94-ae8f-f0a944dd3336

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
theorem _root_.solution (p a b s j N U : ℕ) :
    nextValues p a b s (p^j) (p^j) (a^j) (9^j*N) (9^j*N) (U*(b*s)^j)=
      oldValues (p^(j+1)) (p^(j+1)) (a^(j+1)) (9^(j+1)*N) (9^(j+1)*N) (U*(b*s)^(j+1)) := by
  simp only [nextValues,oldValues,pow_succ,Nat.cast_mul,Nat.cast_pow,List.cons.injEq]
  repeat' constructor
  all_goals ring
end ThreeSum.LightTernaryBudgetStep
