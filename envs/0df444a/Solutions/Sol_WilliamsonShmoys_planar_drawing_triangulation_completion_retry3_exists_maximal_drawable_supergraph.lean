-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_exists_maximal_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:01:52.599021+00:00
-- url     : https://prove2.me/submissions/06bb5f31-c677-43bb-bcda-9977e97cd1bd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edgeSet_ncard
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_le_of_ne

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V => K <= L /\ HasPlanarDrawingOn L /\
      forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L := by
  classical
  obtain ⟨L, hKL, hLDraw, hMaxEdges⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_max_edgeSet_ncard K hDraw
  refine ⟨L, hKL, hLDraw, ?_⟩
  intro M hLM hMDraw
  by_contra hne
  have hStrict :=
    WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_ne L M hLM hne
  exact (Nat.not_lt_of_ge (hMaxEdges M hLM hMDraw)) hStrict