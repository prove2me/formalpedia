-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_maximal_supergraph_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:10:41.506816+00:00
-- url     : https://prove2.me/submissions/3b744117-5bba-4e29-9d3b-ea22e966279b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ L : SimpleGraph V, J ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = L := by
  classical
  let p : SimpleGraph V → Prop := fun G => J ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  obtain ⟨L, _hDec, hL⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2
      ⟨J, le_rfl, hJ⟩
  refine ⟨L, hL.prop.1, hL.prop.2, ?_⟩
  intro K hLK hK
  have hKp : p K := ⟨hL.prop.1.trans hLK, hK⟩
  have hEq : L = K := (hL.le_iff_eq hKp).mp hLK
  exact hEq.symm