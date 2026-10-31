-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:48.907474+00:00
-- url     : https://prove2.me/submissions/aef69aba-dd28-4cb7-b11c-9fe4a99578a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J := by
  classical
  let p : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨J, hJdec, hJ⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := p)).2
      ⟨H, ⟨le_rfl, hPlanar⟩⟩
  letI : DecidableRel J.Adj := hJdec
  have hJgood : H ≤ J ∧ HasPlanarDrawingOn J := hJ.1
  refine ⟨J, hJgood.1, hJgood.2, ?_⟩
  intro K hJK hKplanar
  have hKgood : p K := ⟨le_trans hJgood.1 hJK, hKplanar⟩
  have hJ_eq_K : J = K :=
    (SimpleGraph.IsExtremal.le_iff_eq hJ hKgood).mp hJK
  exact hJ_eq_K.symm ▸ le_rfl