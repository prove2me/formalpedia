-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_by_edge_count__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:56:20.290571+00:00
-- url     : https://prove2.me/submissions/c8e5e5c5-2f85-4c98-b993-ac4218a22b69

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, H.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet.ncard ≥ L.edgeSet.ncard) := by
  classical
  let admissible : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  letI : Finite (SimpleGraph V) := inferInstance
  letI : Finite {G : SimpleGraph V // admissible G} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨K, hK, hmax⟩ :=
    Set.exists_max_image {G : SimpleGraph V | admissible G}
      (fun G => G.edgeSet.ncard)
      (Set.toFinite {G : SimpleGraph V | admissible G})
      ⟨H, by simp [admissible, hH]⟩
  refine ⟨K, ?_, hK.2, ?_⟩
  · intro u v huv
    exact hK.1 huv
  · intro L hHL hL
    exact hmax L ⟨hHL, hL⟩