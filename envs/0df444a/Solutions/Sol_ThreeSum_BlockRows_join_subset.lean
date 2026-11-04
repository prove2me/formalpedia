-- Prove2me | solution 1 for ThreeSum.BlockRows.join_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:33.52719+00:00
-- url     : https://prove2.me/submissions/520cc428-1309-47f2-8ab2-d6f0b428b9c3

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
theorem _root_.solution {J L : ℕ} (I : Finset (Fin J)) {u v : Fin J → Finset (Fin L)}
    (h : ∀ i ∈ I, u i ⊆ v i) : join I u ⊆ join I v := by
  intro ⟨i, x⟩ hx
  obtain ⟨hi, hx⟩ := mem_join.mp hx
  exact mem_join.mpr ⟨hi, h i hi hx⟩
end ThreeSum.BlockRows
