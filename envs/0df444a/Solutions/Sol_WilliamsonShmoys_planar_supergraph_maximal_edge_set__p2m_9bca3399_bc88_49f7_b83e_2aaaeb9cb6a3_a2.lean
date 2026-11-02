-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_edge_set__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:59.916391+00:00
-- url     : https://prove2.me/submissions/463a4457-dbd9-4120-b9c8-d0ddaec1b2d5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_max_cardinality__p2m_6ba26de6_69bc_4fed_ac6d_a483b85550c4_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V), HasPlanarDrawingOn L ∧
      ∃ (dL : DecidableRel L.Adj),
        letI : DecidableRel L.Adj := dL
        K.edgeFinset ⊆ L.edgeFinset ∧
          ∀ (M : SimpleGraph V) [DecidableRel M.Adj],
            HasPlanarDrawingOn M → L.edgeFinset ⊆ M.edgeFinset →
              M.edgeFinset ⊆ L.edgeFinset := by
  obtain ⟨L, hL, dL, hsub, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_max_cardinality__p2m_6ba26de6_69bc_4fed_ac6d_a483b85550c4_a1 K hK
  refine ⟨L, hL, dL, hsub, ?_⟩
  intro M dM hM hLM
  letI : DecidableRel L.Adj := dL
  letI : DecidableRel M.Adj := dM
  have hcard : M.edgeFinset.card ≤ L.edgeFinset.card := hmax M hM hLM
  by_contra hnot
  have hss : L.edgeFinset ⊂ M.edgeFinset :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨hLM, by
        intro heq
        exact hnot (by simpa [heq] using (Finset.Subset.rfl : M.edgeFinset ⊆ M.edgeFinset))⟩
  have hlt : L.edgeFinset.card < M.edgeFinset.card := Finset.card_lt_card hss
  omega