-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawable_edge_bound__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-04T02:19:38.14886+00:00
-- url     : https://prove2.me/submissions/93ee2dd9-d31b-45d1-ad75-d4d3fe0e7f60

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (N : SimpleGraph V) [DecidableRel N.Adj]
      (hN : HasPlanarDrawingOn N)
      (hcard : 3 ≤ Fintype.card V)
      (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → N ≤ K → K ≤ N → N = K),
      3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  intro h
  let N : SimpleGraph (Fin 3) := ⊥
  have hN : HasPlanarDrawingOn N := by
    refine ⟨fun x => ((x.val : ℝ), (0 : ℝ)), fun _ _ _ => (0, 0), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      change ((x.val : ℝ), (0 : ℝ)) = ((y.val : ℝ), (0 : ℝ)) at hxy
      apply Fin.ext
      exact Nat.cast_injective (congrArg Prod.fst hxy)
    · intro u v huv hadj
      simp [N] at hadj
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      simp [N] at hadj
  have hcard : 3 ≤ Fintype.card (Fin 3) := by simp
  have hmax : ∀ K : SimpleGraph (Fin 3), HasPlanarDrawingOn K → N ≤ K → K ≤ N → N = K := by
    intro K hK hNK hKN
    exact le_antisymm hNK hKN
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hedge : @SimpleGraph.edgeFinset (Fin 3) N (N.fintypeEdgeSet) = ∅ := by
    exact (@SimpleGraph.edgeFinset_eq_empty (Fin 3) N (N.fintypeEdgeSet)).2 rfl
  have hbound := h (N := N) hN hcard hmax
  rw [hedge] at hbound
  norm_num at hbound
