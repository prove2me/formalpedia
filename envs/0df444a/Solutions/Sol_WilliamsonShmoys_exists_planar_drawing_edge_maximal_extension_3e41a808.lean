-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_drawing_edge_maximal_extension_3e41a808
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:29:15.093228+00:00
-- url     : https://prove2.me/submissions/21337741-78f8-4a79-83ae-dc86ced6cc68

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    Exists fun H : SimpleGraph V =>
      T ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → H = K := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G =>
      T ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨T, ?_⟩
    simp [S, hT]
  obtain ⟨H, hHS, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hH : T ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHS).2
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hTK : T ≤ K := le_trans hH.1 hHK
  have hKS : K ∈ S := by
    simp [S, hTK, hK]
  by_contra hneq
  have hlt : H < K := lt_of_le_of_ne hHK hneq
  have hcard : H.edgeFinset.card < K.edgeFinset.card := by
    apply Finset.card_lt_card
    exact SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  exact (Nat.not_lt_of_ge (hmax K hKS)) hcard
