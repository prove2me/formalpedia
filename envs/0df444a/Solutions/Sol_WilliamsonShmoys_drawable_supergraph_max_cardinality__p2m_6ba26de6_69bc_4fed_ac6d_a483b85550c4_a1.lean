-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_max_cardinality__p2m_6ba26de6_69bc_4fed_ac6d_a483b85550c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:31.492515+00:00
-- url     : https://prove2.me/submissions/20703e9b-0e81-4ede-9030-ea0eb9b321b4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_card_bound__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
import Theorems.Thm_WilliamsonShmoys_exists_max_edgeFinset_card__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    Exists fun (L : SimpleGraph V) => And (HasPlanarDrawingOn L)
      (Exists fun (dL : DecidableRel L.Adj) =>
        letI : DecidableRel L.Adj := dL
        And (K.edgeFinset ⊆ L.edgeFinset)
          (forall (M : SimpleGraph V) [DecidableRel M.Adj],
            HasPlanarDrawingOn M -> L.edgeFinset ⊆ M.edgeFinset ->
              M.edgeFinset.card <= L.edgeFinset.card)) := by
  obtain ⟨N, hN⟩ :=
    WilliamsonShmoys.edge_card_bound__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1 (V := V)
  exact WilliamsonShmoys.exists_max_edgeFinset_card__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
    K HasPlanarDrawingOn hK N (by
      intro G _ _
      exact hN G)