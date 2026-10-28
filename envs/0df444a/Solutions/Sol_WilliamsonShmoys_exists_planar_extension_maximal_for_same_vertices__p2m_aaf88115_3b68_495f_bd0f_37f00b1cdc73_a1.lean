-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_extension_maximal_for_same_vertices__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:23:51.905254+00:00
-- url     : https://prove2.me/submissions/cc77e5c7-df80-4258-ab39-b0955ee759d2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ HasPlanarDrawingOn H}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨M, hMmem, hMmax⟩ := hSfin.exists_maximal hSne
  refine ⟨M, hMmem.1, hMmem.2, ?_⟩
  intro N hMN hN
  have hNmem : N ∈ S := ⟨hMmem.1.trans hMN, hN⟩
  have hNM : N ≤ M := hMmax hNmem hMN
  exact le_antisymm hNM hMN