-- Prove2me | solution 1 for P2M_Stream__append_extract_drop_29d8f2c46a9f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:21:49.547935+00:00
-- url     : https://prove2.me/submissions/d196005e-a290-4579-b2ed-54909a9f2bb0

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_eq_take_3a08a50f66bd

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {n : ℕ} :
    (xs.extract 0 n) ++ₛ (xs.drop n) = xs := by
  simp only [extract_eq_take, append_take_drop]
end Stream'
