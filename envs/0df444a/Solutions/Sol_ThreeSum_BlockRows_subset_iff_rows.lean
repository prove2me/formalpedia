-- Prove2me | solution 1 for ThreeSum.BlockRows.subset_iff_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:56.013714+00:00
-- url     : https://prove2.me/submissions/63333329-37fb-41a1-9a7e-f5d2df4e9f09

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_subset
attribute [local simp] ThreeSum.BlockRows.mem_row

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L : ℕ} {S T : Finset (Coord J L)} :
    S ⊆ T ↔ ∀ i, row S i ⊆ row T i := by
  constructor
  · exact row_subset
  · intro h ⟨i, x⟩ hx
    exact mem_row.mp (h i (mem_row.mpr hx))
end ThreeSum.BlockRows
