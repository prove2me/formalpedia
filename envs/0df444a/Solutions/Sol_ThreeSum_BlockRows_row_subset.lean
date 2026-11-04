-- Prove2me | solution 1 for ThreeSum.BlockRows.row_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:24.310877+00:00
-- url     : https://prove2.me/submissions/ec3aff5f-b2a0-4537-bef1-f2eefa7a34df

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows
import Theorems.Thm_ThreeSum_BlockRows_mem_row
attribute [local simp] ThreeSum.BlockRows.mem_row

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L : ℕ} {S T : Finset (Coord J L)} (h : S ⊆ T) (i : Fin J) :
    row S i ⊆ row T i := by
  intro x hx
  exact mem_row.mpr (h (mem_row.mp hx))
end ThreeSum.BlockRows
