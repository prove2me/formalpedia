-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:42.467404+00:00
-- url     : https://prove2.me/submissions/194031bd-f48e-4b35-bfbb-54219b7e5421

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simpleGraph_universe__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
import Theorems.Thm_finite_exists_max_rank__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    letI : (forall H : SimpleGraph V, DecidableRel H.Adj) :=
      fun H => Classical.decRel H.Adj
    Exists fun H : SimpleGraph V =>
      G.edgeFinset ⊆ H.edgeFinset ∧
      HasPlanarDrawingOn H ∧
      forall K : SimpleGraph V,
        H.edgeFinset ⊆ K.edgeFinset ->
        HasPlanarDrawingOn K ->
        K.edgeFinset ⊆ H.edgeFinset := by
  classical
  letI : Finite (SimpleGraph V) :=
    finite_simpleGraph_universe__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1 (V := V)
  obtain ⟨H, hH, hmax⟩ :=
    finite_exists_max_rank__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
      (P := fun H : SimpleGraph V =>
        G.edgeFinset ⊆ H.edgeFinset ∧ HasPlanarDrawingOn H)
      (rank := fun H : SimpleGraph V => H.edgeFinset.card)
      ⟨G, ⟨Finset.Subset.rfl, hG⟩⟩
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hKfeasible : G.edgeFinset ⊆ K.edgeFinset ∧ HasPlanarDrawingOn K :=
    ⟨Finset.Subset.trans hH.1 hHK, hK⟩
  have hcard : K.edgeFinset.card ≤ H.edgeFinset.card := hmax K hKfeasible
  have heq : H.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hHK hcard
  exact heq.symm.subset