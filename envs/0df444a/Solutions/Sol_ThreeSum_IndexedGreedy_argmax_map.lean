-- Prove2me | solution 1 for ThreeSum.IndexedGreedy.argmax_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:35.300633+00:00
-- url     : https://prove2.me/submissions/1803c53a-1d19-499a-816d-7d8c4760d22c

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
theorem _root_.solution {α β : Type*} (g : α → β) (f : β → ℕ) (xs : List α) :
    (xs.map g).argmax f = (xs.argmax (f ∘ g)).map g := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.map_append,List.map_singleton,List.argmax_concat,ih,List.argmax_concat]
    cases h : xs.argmax (f ∘ g) with
    | none => rfl
    | some y =>
      simp only [Option.map_some,Function.comp_apply]
      split <;> rfl
end ThreeSum.IndexedGreedy
