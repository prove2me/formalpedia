-- Prove2me | solution 1 for PascalExtremes.G_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:42.165648+00:00
-- url     : https://prove2.me/submissions/0c0f294c-0bd3-4eda-acce-8ff5d64676b7

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
public import Theorems.Thm_PascalExtremes_m_mem_admissibleIndices

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {N m : ℕ} (hm : 0 < m) (hNm : m < N) :
    G N m ≠ 0 := by
  rw [G, Finset.gcd_ne_zero_iff]
  refine ⟨m, m_mem_admissibleIndices hm hNm, ?_⟩
  exact Nat.choose_ne_zero_iff.mpr hNm.le
end PascalExtremes
