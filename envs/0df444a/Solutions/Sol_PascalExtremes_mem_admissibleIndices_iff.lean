-- Prove2me | solution 1 for PascalExtremes.mem_admissibleIndices_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:54:20.461798+00:00
-- url     : https://prove2.me/submissions/b5cdb6b0-ffd5-4b81-941b-13d11e60df2d

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {N m k : ℕ} :
    k ∈ admissibleIndices N m ↔ Admissible N m k := by
  simp only [admissibleIndices, Finset.mem_filter, Finset.mem_range, Admissible]
  constructor
  · rintro ⟨hkN, hkpos, hmk⟩
    exact ⟨hkpos, hkN, hmk⟩
  · rintro ⟨hkpos, hkN, hmk⟩
    exact ⟨hkN, hkpos, hmk⟩
end PascalExtremes
