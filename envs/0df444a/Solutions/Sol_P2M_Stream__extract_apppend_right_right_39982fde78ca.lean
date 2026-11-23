-- Prove2me | solution 1 for P2M_Stream__extract_apppend_right_right_39982fde78ca
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:25.996194+00:00
-- url     : https://prove2.me/submissions/46350392-2558-401b-a735-1737a4400c84

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__drop_append_of_ge_length_8fcd0b978030

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xl : List X} {xs : Stream' X} {m n : ℕ} (h : xl.length ≤ m) :
    (xl ++ₛ xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := by
  have h1 : n - xl.length - (m - xl.length) = n - m := by omega
  simp (disch := omega) only [extract_eq_drop_take, drop_append_of_ge_length, h1]
end Stream'
