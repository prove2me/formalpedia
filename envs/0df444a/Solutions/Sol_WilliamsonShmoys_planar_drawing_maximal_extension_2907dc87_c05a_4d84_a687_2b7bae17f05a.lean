-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:10:34.613485+00:00
-- url     : https://prove2.me/submissions/a0458183-3df1-4379-998c-741789ff2128

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨G, le_rfl, hG⟩
  exact ⟨H, hH.prop.1, hH.prop.2,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hH.prop.1) (Set.toFinite _),
    fun K hK hPK => le_antisymm (hH.2 ⟨le_trans hH.prop.1 hK, hPK⟩ hK) hK⟩
