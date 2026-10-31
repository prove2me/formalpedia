-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:20.242717+00:00
-- url     : https://prove2.me/submissions/bdf4fc6f-0ead-4b58-8a3a-15734374b117

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_nonempty_has_maximal__p2m_4ded7af1_c0ed_47aa_b513_64b98071a5c3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L := by
  classical
  let P : SimpleGraph V → Prop := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hP : ∃ G, P G := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hLP, hLmax⟩ :=
    finite_nonempty_has_maximal__p2m_4ded7af1_c0ed_47aa_b513_64b98071a5c3_a1
      (α := SimpleGraph V) P hP
  exact ⟨L, hLP.1, hLP.2, fun N hLN hN => hLmax N ⟨le_trans hLP.1 hLN, hN⟩ hLN⟩