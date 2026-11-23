-- Prove2me | solution 1 for P2M_Stream__drop_append_of_ge_length_8fcd0b978030
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:31:49.966797+00:00
-- url     : https://prove2.me/submissions/e0562484-e27d-4e1c-a32f-90ef16c7f50e

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63
import Theorems.Thm_P2M_Stream__get_append_right__3668139ab712

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).drop n = xs.drop (n - xl.length) := by
  ext k ; simp (disch := omega) only [get.eq_1, get_drop', get_append_right']
  congr ; omega
end Stream'
