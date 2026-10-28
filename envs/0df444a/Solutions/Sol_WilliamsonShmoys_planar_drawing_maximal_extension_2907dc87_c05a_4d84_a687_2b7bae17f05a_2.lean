-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:10:53.9351+00:00
-- url     : https://prove2.me/submissions/704c228b-34b2-40ef-82f0-2029983f0061

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
  obtain ⟨H, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hG
  exact ⟨H, hMH, hmax.1, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMH) (Set.toFinite _),
    fun K hK hKp => le_antisymm (hmax.2 hKp hK) hK⟩
