-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_from_drawing_cd0a3fa1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:25:30.480044+00:00
-- url     : https://prove2.me/submissions/1d025946-5d8b-4612-b367-b115787ff6cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_from_drawing
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      (∀ ⦃u v : V⦄, K.Adj u v → G.Adj u v)) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  let b : Nat := 3 * Fintype.card V - 6
  have hup :
      G.edgeSet.ncard ≤ b :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_from_drawing G hG hV
  have hlow : b ≤ G.edgeSet.ncard := by
    by_contra hnot
    have hlt : G.edgeSet.ncard < b := Nat.lt_of_not_ge hnot
    obtain ⟨K, hsub, hK, u, v, huvK, huvnot⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_below_bound G hG hV hlt
    exact huvnot (hmax K hsub hK huvK)
  dsimp [b] at hup hlow ⊢
  exact Nat.le_antisymm hup hlow
