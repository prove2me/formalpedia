-- Prove2me | solution 1 for P2M_Stream__extract_eq_nil_iff_c45b6d031ac4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:31:51.857532+00:00
-- url     : https://prove2.me/submissions/12f5a01a-e48d-4250-a816-b56ebbd105aa

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = [] ↔ m ≥ n := by
  simp only [extract_eq_drop_take, ← List.length_eq_zero_iff, length_take, ge_iff_le]
  omega
end Stream'
