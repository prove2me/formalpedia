-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:50:14.389686+00:00
-- url     : https://prove2.me/submissions/7b478e07-72f7-483d-b1f4-d0cccef462c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

namespace S220WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

theorem sub_draw {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hle : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv hA => h1 u v huv (hle hA),
    fun u v x y huv hxy hA hB => h2 u v x y huv hxy (hle hA) (hle hB)⟩

theorem one_edge {V : Type} [Fintype V] (K L : SimpleGraph V) (hKL : K ≤ L) (hne : K ≠ L) :
    ∃ M : SimpleGraph V, K ≤ M ∧ M ≤ L ∧ M.edgeSet.ncard = K.edgeSet.ncard + 1 := by
  have hne' : (L.edgeSet \ K.edgeSet).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    exact hne (le_antisymm hKL (SimpleGraph.edgeSet_subset_edgeSet.mp h))
  obtain ⟨e, heL, heK⟩ := hne'
  have hnd : ¬ e.IsDiag := L.not_isDiag_of_mem_edgeSet heL
  let H := SimpleGraph.fromEdgeSet (insert e K.edgeSet)
  have hH : H.edgeSet = insert e K.edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff]
    constructor
    · exact fun h => h.1
    · rintro (rfl | hx)
      · exact ⟨Or.inl rfl, hnd⟩
      · exact ⟨Or.inr hx, K.not_isDiag_of_mem_edgeSet hx⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [← SimpleGraph.edgeSet_subset_edgeSet, hH]; exact Set.subset_insert _ _
  · rw [← SimpleGraph.edgeSet_subset_edgeSet, hH]
    exact Set.insert_subset heL (SimpleGraph.edgeSet_subset_edgeSet.mpr hKL)
  · rw [hH, Set.ncard_insert_of_notMem heK (Set.toFinite _)]

end S220WS


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := S220WS.exists_maximal N _ hDraw
