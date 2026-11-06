-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_has_maximal_supergraph__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:04:01.505894+00:00
-- url     : https://prove2.me/submissions/9c2500a4-0137-4d24-ad2a-e2ae4305d005

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  let p : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hpH : p H := ⟨le_rfl, hH⟩
  obtain ⟨K, _hHK, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH)
  rcases hmax with ⟨hpK, hmax'⟩
  have hsub : H.edgeSet ⊆ K.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hpK.1
  have hfin : K.edgeSet.Finite := Set.toFinite _
  refine ⟨K, hpK.1, hpK.2, Set.ncard_le_ncard hsub hfin, ?_⟩
  intro L hKL hL
  exact hmax' ⟨hpK.1.trans hKL, hL⟩ hKL
