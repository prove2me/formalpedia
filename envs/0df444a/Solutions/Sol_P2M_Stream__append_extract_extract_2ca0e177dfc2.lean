-- Prove2me | solution 1 for P2M_Stream__append_extract_extract_2ca0e177dfc2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:33.972566+00:00
-- url     : https://prove2.me/submissions/cd4d3463-4178-4868-b256-0837d5ee96f6

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs.extract k m) ++ (xs.extract m n) = xs.extract k n := by
  have h1 : n - k = (m - k) + (n - m) := by omega
  have h2 : k + (m - k) = m := by omega
  simp only [extract_eq_drop_take, h1, take_add, drop_drop, h2]
end Stream'
