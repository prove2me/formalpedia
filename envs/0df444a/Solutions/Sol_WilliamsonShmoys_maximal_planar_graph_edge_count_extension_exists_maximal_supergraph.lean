-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_extension_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:40:33.305189+00:00
-- url     : https://prove2.me/submissions/7df2291b-fe55-4ba4-8ba8-467020a6d9f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V => K ≤ L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  obtain ⟨L, hL⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨K, le_rfl, hK⟩
  obtain ⟨instL, hExt⟩ := hL
  letI := instL
  refine ⟨L, hExt.1.1, hExt.1.2, ?_⟩
  intro M hLM hM
  have hMp : p M := ⟨hExt.1.1.trans hLM, hM⟩
  have hEq : L = M :=
    (SimpleGraph.IsExtremal.le_iff_eq hExt hMp).1 hLM
  exact hEq.symm ▸ le_rfl
