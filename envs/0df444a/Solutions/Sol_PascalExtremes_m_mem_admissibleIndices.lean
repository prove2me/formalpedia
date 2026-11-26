-- Prove2me | solution 1 for PascalExtremes.m_mem_admissibleIndices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:02.959837+00:00
-- url     : https://prove2.me/submissions/5a5d1658-97f2-42a9-bf4a-afe59dd1f5a4

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {N m : ℕ} (hm : 0 < m) (hmN : m < N) :
    m ∈ admissibleIndices N m := by
  simp [admissibleIndices, hm, hmN]
end PascalExtremes
