-- Prove2me | solution 1 for P2M_Stream__get_append_right__3668139ab712
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:17:49.627783+00:00
-- url     : https://prove2.me/submissions/54d7f514-0da1-47d3-bae6-0c58b7a6305c

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xl : List X} {xs : Stream' X} {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ₛ xs) k = xs (k - xl.length) := by
  obtain ⟨n, rfl⟩ := show ∃ n, k = xl.length + n by use (k - xl.length) ; omega
  simp ; apply get_append_right
end Stream'
