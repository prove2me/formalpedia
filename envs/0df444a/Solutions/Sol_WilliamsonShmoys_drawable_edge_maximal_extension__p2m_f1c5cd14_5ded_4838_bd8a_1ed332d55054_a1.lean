-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edge_maximal_extension__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:36.232197+00:00
-- url     : https://prove2.me/submissions/af4b8dc5-085c-4e24-bf96-af09ea044a49

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V, exists instH : DecidableRel H.Adj,
      (letI : DecidableRel H.Adj := instH
       G.edgeFinset ⊆ H.edgeFinset /\
       HasPlanarDrawingOn H /\
       ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
         H.edgeFinset ⊆ K.edgeFinset → HasPlanarDrawingOn K →
           K.edgeFinset ⊆ H.edgeFinset) := by
  classical
  let p : SimpleGraph V → Prop := fun X => G ≤ X ∧ HasPlanarDrawingOn X
  have hbase : p G := ⟨le_rfl, hG⟩
  obtain ⟨H, instH, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := p)).2 ⟨G, hbase⟩
  refine ⟨H, instH, ?_⟩
  letI : DecidableRel H.Adj := instH
  refine ⟨SimpleGraph.edgeFinset_subset_edgeFinset.mpr hmax.1.1,
    hmax.1.2, ?_⟩
  intro K instK hHK hK
  letI : DecidableRel K.Adj := instK
  have hle : H ≤ K := SimpleGraph.edgeFinset_subset_edgeFinset.mp hHK
  have hKp : p K := ⟨hmax.1.1.trans hle, hK⟩
  have heq : H = K := (SimpleGraph.IsExtremal.le_iff_eq hmax hKp).mp hle
  have hrev : K ≤ H := le_of_eq heq.symm
  exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hrev