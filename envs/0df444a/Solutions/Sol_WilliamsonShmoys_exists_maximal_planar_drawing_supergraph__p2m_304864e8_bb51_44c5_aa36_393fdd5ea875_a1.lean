-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:57.502442+00:00
-- url     : https://prove2.me/submissions/a431d0a8-e8e6-4dec-9d71-b3eff98d935a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V, Y.edgeSet ⊂ Z.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn Z := by
  classical
  let S : Set (SimpleGraph V) :=
    {Y | X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨Y, hY, hmax⟩ :=
    hSfinite.exists_maximal (show S.Nonempty from ⟨X, le_rfl, hX⟩)
  refine ⟨Y, ?_, hY.2, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hY.1
  · intro Z hYZ hZ
    have hYZle : Y ≤ Z := (SimpleGraph.edgeSet_ssubset_edgeSet.mp hYZ).le
    have hZS : Z ∈ S := ⟨le_trans hY.1 hYZle, hZ⟩
    have hZY : Z ≤ Y := hmax hZS hYZle
    have hnotZY : ¬ Z ≤ Y := by
      intro h
      exact hYZ.2 (SimpleGraph.edgeSet_subset_edgeSet.mpr h)
    exact hnotZY hZY