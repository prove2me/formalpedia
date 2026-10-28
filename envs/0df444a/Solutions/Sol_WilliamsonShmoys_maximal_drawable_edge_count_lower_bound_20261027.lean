-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:25:09.243413+00:00
-- url     : https://prove2.me/submissions/cfcc1338-a7dd-4fa0-b29d-c1a25a11bc57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_edge_count_20261027

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hGmax : forall K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K.edgeSet ⊆ G.edgeSet) :
    3 * Fintype.card V <= G.edgeSet.ncard + 6 := by
  classical
  obtain ⟨K, hGK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_edge_count_20261027
      G hV hGplanar
  have hKG : K.edgeSet ⊆ G.edgeSet := hGmax K hGK hKplanar
  have hsets : G.edgeSet = K.edgeSet := Set.Subset.antisymm hGK hKG
  have hcount : G.edgeSet.ncard = K.edgeSet.ncard :=
    congrArg Set.ncard hsets
  rw [← hcount] at hKcount
  omega
