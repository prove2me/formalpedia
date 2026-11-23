-- Prove2me | solution 1 for P2M_Stream__extract_append_zero_right_6dd07cb04cbe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:21:51.580176+00:00
-- url     : https://prove2.me/submissions/9884da4e-527c-44cb-8507-bd26895bdcf6

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_eq_take_3a08a50f66bd

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).extract 0 n = xl ++ (xs.extract 0 (n - xl.length)) := by
  obtain ⟨k, rfl⟩ := show ∃ k, n = xl.length + k by use (n - xl.length) ; omega
  simp only [extract_eq_take, ← append_take, add_tsub_cancel_left]
end Stream'
