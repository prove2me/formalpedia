-- Prove2me | solution 1 for SZ.node_used_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:34.944469+00:00
-- url     : https://prove2.me/submissions/01376f6b-d984-4fba-96fd-a58bd9d57503

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_used_succ_branch
import Theorems.Thm_SZ_node_used_succ_not

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) :
    (node β j).used ≤ (node β k).used := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    by_cases hb : Branching (node β k)
    · rw [node_used_succ_branch β hb]; omega
    · rw [node_used_succ_not β hb]; exact ih
end SZ
