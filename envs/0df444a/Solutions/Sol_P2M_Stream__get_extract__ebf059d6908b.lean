-- Prove2me | solution 1 for P2M_Stream__get_extract__ebf059d6908b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:27.800874+00:00
-- url     : https://prove2.me/submissions/2bbd2193-a65b-4e59-baba-e7b18e4ef12b

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__get_extract_66835107dc16

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs (m + k) := by
  apply get_extract h
end Stream'
