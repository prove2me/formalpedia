-- Prove2me | solution 1 for ThreeSum.BlockRows.join_disjoint_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:32.483111+00:00
-- url     : https://prove2.me/submissions/fdcb6bfe-30fe-44e8-b953-e5ce18a8d6a2

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows
import Theorems.Thm_ThreeSum_BlockRows_mem_join
attribute [local simp] ThreeSum.BlockRows.mem_join

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (join I u) (join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (mem_join.mp hy).1) (mem_join.mp hx).1
end ThreeSum.BlockRows
