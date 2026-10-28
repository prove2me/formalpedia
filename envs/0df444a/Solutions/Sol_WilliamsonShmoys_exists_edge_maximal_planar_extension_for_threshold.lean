-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension_for_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:45:18.356228+00:00
-- url     : https://prove2.me/submissions/b6604412-7719-4e42-aedc-7910b021d58c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.finite_univ.subset (by
    intro G hG
    exact Set.mem_univ G)
  have hSnonempty : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨M, hMmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨M, hMmax.prop.1, hMmax.prop.2, ?_⟩
  intro N hMN hN
  have hNmem : N ∈ S := ⟨hMmax.prop.1.trans hMN, hN⟩
  exact (hMmax.eq_of_le hNmem hMN).symm