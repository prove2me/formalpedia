-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_from_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:07:30.890725+00:00
-- url     : https://prove2.me/submissions/b8e85fe0-5761-4808-a667-09d87c7c8f09

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

private theorem hasPlanarDrawingOn_mono
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hArc, hCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hArc u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs hEq
    exact hCross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs hEq

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hE : M.edgeSet.ncard < 3 * Fintype.card V - 6)
    (hT : ∃ T : SimpleGraph V, M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  obtain ⟨T, hMT, hTPlanar, hTCount⟩ := hT
  have hCountLt : M.edgeSet.ncard < T.edgeSet.ncard := by
    rw [hTCount]
    exact hE
  have hNotSub : ¬ T.edgeSet ⊆ M.edgeSet := by
    intro hSub
    have hLe : T.edgeSet.ncard ≤ M.edgeSet.ncard := Set.ncard_le_ncard hSub
    omega
  have hExists : ∃ e, e ∈ T.edgeSet ∧ e ∉ M.edgeSet := by
    by_contra h
    apply hNotSub
    intro e heT
    by_contra heM
    exact h ⟨e, heT, heM⟩
  obtain ⟨e, heT, heM⟩ := hExists
  let E : SimpleGraph V := SimpleGraph.fromEdgeSet ({e} : Set (Sym2 V))
  let N : SimpleGraph V := M ⊔ E
  have hET : E ≤ T := by
    change SimpleGraph.fromEdgeSet ({e} : Set (Sym2 V)) ≤ T
    rw [SimpleGraph.fromEdgeSet_le]
    intro x hx
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hx
    rcases hx with ⟨rfl, _⟩
    exact heT
  have hNT : N ≤ T := sup_le hMT hET
  have hMN : M ≤ N := le_sup_left
  have hNPlanar : WilliamsonShmoys.HasPlanarDrawingOn N :=
    hasPlanarDrawingOn_mono N T hNT hTPlanar
  have heNotDiag : e ∉ Sym2.diagSet :=
    SimpleGraph.not_isDiag_of_mem_edgeSet T heT
  have hEedge : E.edgeSet = {e} := by
    change (SimpleGraph.fromEdgeSet ({e} : Set (Sym2 V))).edgeSet = {e}
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact hx.1
    · intro hx
      subst x
      exact ⟨rfl, heNotDiag⟩
  have hNEdges : N.edgeSet = insert e M.edgeSet := by
    change (M ⊔ E).edgeSet = insert e M.edgeSet
    rw [SimpleGraph.edgeSet_sup, hEedge]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  refine ⟨N, hMN, hNPlanar, ?_⟩
  rw [hNEdges, Set.ncard_insert_of_notMem heM]