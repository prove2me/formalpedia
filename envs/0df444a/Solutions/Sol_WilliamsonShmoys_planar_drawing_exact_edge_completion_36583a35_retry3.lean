-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_completion_36583a35_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:55:22.871467+00:00
-- url     : https://prove2.me/submissions/2efc26ed-d222-43bd-8c0d-a6593295fdae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_retry3
import Theorems.Thm_WilliamsonShmoys_finite_graph_edge_augmentation_saturation_retry3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V,
      L <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  let M : Nat := 3 * Fintype.card V - 6
  have hBound : forall G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G -> G.edgeSet.ncard <= M := by
    intro G hG
    have h := WilliamsonShmoys.planar_edge_count_bound_retry3 G hG hCard
    dsimp [M]
    omega
  have hAugment : forall G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G ->
      G.edgeSet.ncard < M ->
      exists H : SimpleGraph V, G <= H /\
        WilliamsonShmoys.HasPlanarDrawingOn H /\
        H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
    intro G hG hCount
    exact WilliamsonShmoys.planar_edge_augmentation_retry3 G hG hCard (by
      simpa [M] using hCount)
  obtain ⟨K, hLK, hK, hCount⟩ :=
    WilliamsonShmoys.finite_graph_edge_augmentation_saturation_retry3
      (P := WilliamsonShmoys.HasPlanarDrawingOn)
      (L := L) (M := M) hL hBound hAugment
  refine ⟨K, hLK, hK, ?_⟩
  calc
    (K.edgeSet.ncard : Int) = (M : Int) := by exact_mod_cast hCount
    _ = 3 * (Fintype.card V : Int) - 6 := by
      dsimp [M]
      omega
