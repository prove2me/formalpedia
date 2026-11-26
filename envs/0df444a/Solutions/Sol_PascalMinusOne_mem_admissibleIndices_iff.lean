-- Prove2me | solution 1 for PascalMinusOne.mem_admissibleIndices_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:17:18.546984+00:00
-- url     : https://prove2.me/submissions/4e356b2c-9ac7-47db-a947-bc71c429ed18

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {N m k : ℕ} :
    k ∈ admissibleIndices N m ↔ Admissible N m k := by
  simp only [admissibleIndices, Finset.mem_filter, Finset.mem_range, Admissible]
  constructor
  · rintro ⟨hkN, hkpos, hmk⟩
    exact ⟨hkpos, hkN, hmk⟩
  · rintro ⟨hkpos, hkN, hmk⟩
    exact ⟨hkN, hkpos, hmk⟩
end PascalMinusOne
