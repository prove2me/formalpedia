-- Prove2me | solution 1 for SZ.exists_branch_at_used
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:47.387964+00:00
-- url     : https://prove2.me/submissions/53730216-66b2-41e9-b159-5c4919ac94f3

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_used_zero
import Theorems.Thm_SZ_node_used_succ_branch
import Theorems.Thm_SZ_node_used_succ_not
import Theorems.Thm_SZ_node_used_unbounded

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (n : ℕ) :
    ∃ k, (node β k).used = n ∧ Branching (node β k) := by
  classical
  have hex : ∃ k, n < (node β k).used := node_used_unbounded β n
  have h1 : n < (node β (Nat.find hex)).used := Nat.find_spec hex
  have h2 : Nat.find hex ≠ 0 := by
    intro hz
    rw [hz, node_used_zero] at h1
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have h3 : ¬ (n < (node β k).used) := Nat.find_min hex (by omega)
  rw [hk] at h1
  by_cases hb : Branching (node β k)
  · rw [node_used_succ_branch β hb] at h1
    exact ⟨k, by omega, hb⟩
  · rw [node_used_succ_not β hb] at h1
    omega
end SZ
