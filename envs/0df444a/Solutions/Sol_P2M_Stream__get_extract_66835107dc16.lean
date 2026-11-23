-- Prove2me | solution 1 for P2M_Stream__get_extract_66835107dc16
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:31:52.3402+00:00
-- url     : https://prove2.me/submissions/14916a4d-f18c-4cef-924f-a8a579440935

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs.get (m + k) := by
  simp only [extract_eq_drop_take, take_get, get_drop]
end Stream'
