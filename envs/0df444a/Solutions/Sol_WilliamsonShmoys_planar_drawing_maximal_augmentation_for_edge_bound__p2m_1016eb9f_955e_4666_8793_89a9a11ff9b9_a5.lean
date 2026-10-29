-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_augmentation_for_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:24:25.293688+00:00
-- url     : https://prove2.me/submissions/a3fe14e1-06d1-4228-8939-6e179731d639

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      And (K <= L) (And (WilliamsonShmoys.HasPlanarDrawingOn L)
        (forall M : SimpleGraph V, L <= M ->
          WilliamsonShmoys.HasPlanarDrawingOn M -> M <= L)) := by
  classical
  letI : Finite (SimpleGraph V) :=
    Finite.of_injective
      (fun G : SimpleGraph V => fun v w => decide (G.Adj v w))
      (by
        intro G H h
        ext v w
        have hvw := congrFun (congrFun h v) w
        simpa using hvw)
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => And (K <= G) (WilliamsonShmoys.HasPlanarDrawingOn G)
  have hS : S.Nonempty := by
    refine Exists.intro K ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro le_rfl hK
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hLspec : And (K <= L) (WilliamsonShmoys.HasPlanarDrawingOn L) := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hLmem
  refine Exists.intro L (And.intro hLspec.1 (And.intro hLspec.2 ?_))
  intro M hLM hM
  have hMmem : M ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro (hLspec.1.trans hLM) hM
  have hEdges : L.edgeFinset ⊆ M.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hLM
  have hCardLE : L.edgeFinset.card <= M.edgeFinset.card := Finset.card_le_card hEdges
  have hCardGE : M.edgeFinset.card <= L.edgeFinset.card := hLmax M hMmem
  have hCard : L.edgeFinset.card = M.edgeFinset.card := Nat.le_antisymm hCardLE hCardGE
  have hEdgeEq : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hEdges (by simpa [hCard])
  apply (SimpleGraph.edgeFinset_subset_edgeFinset).1
  rw [← hEdgeEq]