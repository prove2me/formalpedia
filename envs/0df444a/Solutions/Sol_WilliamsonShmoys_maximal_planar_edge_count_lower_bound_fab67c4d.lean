-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fab67c4d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:37:33.845591+00:00
-- url     : https://prove2.me/submissions/b140e5fb-8258-4ce6-b36e-219fe8f4d0cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_fab67c4d

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn M) :
    3 * (Fintype.card V : Int) - 6 ≤ (L.edgeSet.ncard : Int) := by
  obtain ⟨M, hM, hLM, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_fab67c4d L hL hCard
  have hEdgeSets : L.edgeSet = M.edgeSet := by
    by_contra hne
    exact hMax M (Set.ssubset_iff_subset_ne.mpr ⟨hLM, hne⟩) hM
  have hNcard : L.edgeSet.ncard = M.edgeSet.ncard := congrArg Set.ncard hEdgeSets
  have hIntNcard : (L.edgeSet.ncard : Int) = (M.edgeSet.ncard : Int) :=
    congrArg (fun n : Nat => (n : Int)) hNcard
  exact le_of_eq (hCount.trans hIntNcard.symm)