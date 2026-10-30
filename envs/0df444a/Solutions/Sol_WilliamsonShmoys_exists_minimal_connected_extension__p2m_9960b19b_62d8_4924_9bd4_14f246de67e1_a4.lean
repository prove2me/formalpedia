-- Prove2me | solution 1 for WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:53:26.231988+00:00
-- url     : https://prove2.me/submissions/7d5aa6ae-5199-4987-97ef-22cd5f0fcddd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_minimal_connected_extension_exists__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
import Theorems.Thm_WilliamsonShmoys_delete_edge_path_connected__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (M : SimpleGraph V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
      ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
        ¬ (H.deleteEdges {s(u, v)}).Reachable u v := by
  obtain ⟨H, hMH, hconn, hmin⟩ :=
    WilliamsonShmoys.minimal_connected_extension_exists__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1 M
  refine ⟨H, hMH, hconn, ?_⟩
  intro u v huv hnotM hreach
  have hdelconn := WilliamsonShmoys.delete_edge_path_connected__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
    (H := H) (u := u) (v := v) hconn hreach
  have hsub : H.deleteEdges {s(u, v)} ≤ H :=
    SimpleGraph.deleteEdges_le _
  have hcontain : M ≤ H.deleteEdges {s(u, v)} := by
    intro a b hab
    have hHab : H.Adj a b := hMH hab
    have hnotmem : s(a, b) ∉ ({s(u, v)} : Set (Sym2 V)) := by
      simp only [Set.mem_singleton_iff]
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
      · subst a
        subst b
        exact hnotM hab
      · subst a
        subst b
        exact hnotM (SimpleGraph.Adj.symm hab)
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hHab, hnotmem⟩
  have hle := hmin (H.deleteEdges {s(u, v)}) hcontain hsub hdelconn
  have hdelnot : ¬ (H.deleteEdges {s(u, v)}).Adj u v := by
    simp
  exact hdelnot (hle huv)