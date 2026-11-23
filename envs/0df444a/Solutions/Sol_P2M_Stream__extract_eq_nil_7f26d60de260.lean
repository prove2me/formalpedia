-- Prove2me | solution 1 for P2M_Stream__extract_eq_nil_7f26d60de260
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:12:51.851153+00:00
-- url     : https://prove2.me/submissions/98d62153-239b-4658-8670-ecb0c236147b

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {n : ℕ} :
    xs.extract n n = [] := by
  simp only [extract_eq_drop_take, tsub_self, take_zero]
end Stream'
