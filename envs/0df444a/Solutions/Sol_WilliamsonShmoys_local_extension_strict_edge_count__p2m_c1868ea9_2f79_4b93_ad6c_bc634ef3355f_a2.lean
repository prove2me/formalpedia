-- Prove2me | solution 1 for WilliamsonShmoys.local_extension_strict_edge_count__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:18:48.283362+00:00
-- url     : https://prove2.me/submissions/9c46ceff-fe04-4c4a-abf3-fbe64c3e15b5

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : ¬ G.Reachable u v)
    (H : SimpleGraph V) (hGH : G ≤ H)
    (hadj : ∀ x y : V,
      H.Adj x y ↔
        G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    G.edgeSet.ncard < H.edgeSet.ncard := by
  classical
  have hHuv : H.Adj u v := by
    rw [hadj u v]
    simp
  have hGuv : ¬ G.Adj u v := fun h => huv h.reachable
  have hne : G ≠ H := by
    intro hEq
    exact hGuv (by simpa [hEq] using hHuv)
  have hltGH : G < H := lt_of_le_of_ne hGH hne
  have hss : G.edgeSet ⊂ H.edgeSet := (SimpleGraph.edgeSet_ssubset_edgeSet).2 hltGH
  exact Set.ncard_lt_ncard hss (Set.toFinite _)
