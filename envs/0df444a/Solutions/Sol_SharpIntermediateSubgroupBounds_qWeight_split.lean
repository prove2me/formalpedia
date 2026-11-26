-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qWeight_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:24.372168+00:00
-- url     : https://prove2.me/submissions/488328a7-c7b5-48e8-b454-40ee6c938833

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_qWeight_succ

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution : ∀ {n k : ℕ}, k ≤ n →
    qWeight n = qWeight k + qWeight (n - k) + k * (n - k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          rw [qWeight_succ, qWeight_succ, Nat.succ_sub_succ_eq_sub, ih hkn]
          have hn : n + 1 = (k + 1) + (n - k) := by omega
          rw [hn]
          ring
end SharpIntermediateSubgroupBounds
