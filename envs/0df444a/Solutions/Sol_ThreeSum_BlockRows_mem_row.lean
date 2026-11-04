-- Prove2me | solution 1 for ThreeSum.BlockRows.mem_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:19.790181+00:00
-- url     : https://prove2.me/submissions/6e04af92-d2ef-46b2-b59d-2a90ad24ef02

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_flat

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L : ℕ} {S : Finset (Coord J L)} {i : Fin J} {x : Fin L} :
    x ∈ row S i ↔ Sigma.mk i x ∈ S := by
  simp only [row, Finset.mem_filter, Finset.mem_univ, true_and]
end ThreeSum.BlockRows
