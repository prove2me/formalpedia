-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_max_edge_card__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:08.545279+00:00
-- url     : https://prove2.me/submissions/cfbac02a-30cf-4646-846f-ca54d0770f66

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_card_of_predicate__p2m_8f4450fd_25bb_4306_b9c5_7a9c9b261a7b_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, N ≤ L → HasPlanarDrawingOn L →
        Nat.card {e : Sym2 V // e ∈ L.edgeSet} ≤
          Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by
  classical
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_max_card_of_predicate__p2m_8f4450fd_25bb_4306_b9c5_7a9c9b261a7b_a2
      (α := SimpleGraph V)
      (P := fun G => N ≤ G ∧ HasPlanarDrawingOn G)
      (f := fun G => Nat.card {e : Sym2 V // e ∈ G.edgeSet})
      ⟨N, le_rfl, hN⟩
  exact ⟨K, hK.1, hK.2, fun L hNL hL => hmax L ⟨hNL, hL⟩⟩