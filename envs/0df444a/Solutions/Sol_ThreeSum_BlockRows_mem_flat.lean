-- Prove2me | solution 1 for ThreeSum.BlockRows.mem_flat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:31.493444+00:00
-- url     : https://prove2.me/submissions/c6f0e27e-3d36-4c13-8ded-0fc5267b45b2

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
theorem _root_.solution {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ flat u ↔ x ∈ u i := by
  simp only [flat, mem_join, Finset.mem_univ, true_and]
end ThreeSum.BlockRows
