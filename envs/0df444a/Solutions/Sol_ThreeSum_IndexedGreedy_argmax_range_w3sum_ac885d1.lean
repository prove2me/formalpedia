-- Prove2me | solution 1 for ThreeSum.IndexedGreedy.argmax_range_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:38.545758+00:00
-- url     : https://prove2.me/submissions/44a89468-ee30-4b5e-8ce8-4264cf07cdf2

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
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
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum
namespace ThreeSum.IndexedGreedy
theorem _root_.solution (f : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    (List.range n).argmax f = some (least (fun i => -(f i : ℤ)) n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [least]
    | succ n =>
      rw [List.range_succ,List.argmax_concat,ih (by omega)]
      change (if f (least (fun i => -(f i : ℤ)) (n+1)) < f (n+1)
        then some (n+1) else some (least (fun i => -(f i : ℤ)) (n+1))) =
        some (if -(f (n+1) : ℤ) < -(f (least (fun i => -(f i : ℤ)) (n+1)) : ℤ)
          then n+1 else least (fun i => -(f i : ℤ)) (n+1))
      split_ifs <;> first | rfl | omega
end ThreeSum.IndexedGreedy
