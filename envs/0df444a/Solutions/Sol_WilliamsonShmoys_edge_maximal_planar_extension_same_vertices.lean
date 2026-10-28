-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_extension_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:40:56.522042+00:00
-- url     : https://prove2.me/submissions/76456cb2-152b-46df-b0c0-aee6a7ef4799

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard <= H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard <= H.edgeSet.ncard := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image _ (fun J : SimpleGraph V => J.edgeSet.ncard) hfin
    ⟨G, le_rfl, hG⟩
  refine ⟨M, hmax G ⟨le_rfl, hG⟩, hM.2, fun K hK hP => hmax K ⟨le_trans hM.1 (fun u v h => hK h), hP⟩⟩
