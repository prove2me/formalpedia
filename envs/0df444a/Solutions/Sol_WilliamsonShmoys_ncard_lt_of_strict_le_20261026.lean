-- Prove2me | solution 1 for WilliamsonShmoys.ncard_lt_of_strict_le_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:30:38.570878+00:00
-- url     : https://prove2.me/submissions/320abd33-3d25-4424-b150-4d23a1009e2b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (M N : SimpleGraph V)
    (hMN : M <= N)
    (hne : N ≠ M) :
    M.edgeSet.ncard < N.edgeSet.ncard := by
  classical
  have hproper : M.edgeSet ⊂ N.edgeSet := by
    rw [SimpleGraph.edgeSet_ssubset_edgeSet]
    exact ⟨hMN, fun hNM => hne (le_antisymm hNM hMN)⟩
  have hfinite : N.edgeSet.Finite := Set.finite_univ.subset (Set.subset_univ _)
  exact Set.ncard_lt_ncard hproper hfinite