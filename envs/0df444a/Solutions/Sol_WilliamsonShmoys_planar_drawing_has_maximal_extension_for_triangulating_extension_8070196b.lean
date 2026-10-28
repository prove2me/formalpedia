-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulating_extension_8070196b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:19:48.378069+00:00
-- url     : https://prove2.me/submissions/0ed390d9-cdeb-496a-bdf5-4e47d577d868

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V,
        U.edgeSet ⊆ W.edgeSet →
        HasPlanarDrawingOn W →
        W.edgeSet ⊆ U.edgeSet := by
  classical
  let S : Set (SimpleGraph V) := {U | T ≤ U ∧ HasPlanarDrawingOn U}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨T, le_rfl, hT⟩
  obtain ⟨U, hUmax⟩ := hSfinite.exists_maximal hSne
  refine ⟨U, ?_, ?_, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.2 (hUmax.1.1)
  · exact hUmax.1.2
  · intro W hUW hW
    have hWmem : W ∈ S := ⟨le_trans (hUmax.1.1) (SimpleGraph.edgeSet_subset_edgeSet.1 hUW), hW⟩
    exact SimpleGraph.edgeSet_subset_edgeSet.2 (hUmax.2 hWmem (SimpleGraph.edgeSet_subset_edgeSet.1 hUW))