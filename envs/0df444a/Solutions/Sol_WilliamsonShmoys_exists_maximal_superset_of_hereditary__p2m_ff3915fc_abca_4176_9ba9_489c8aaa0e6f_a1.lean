-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_superset_of_hereditary__p2m_ff3915fc_abca_4176_9ba9_489c8aaa0e6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:00:44.715991+00:00
-- url     : https://prove2.me/submissions/571c16a8-0fa7-4570-9bb5-411c77b8ebbf

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
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V},
      (∀ u v, G.Adj u v → H.Adj u v) → P H → P G)
    (S : SimpleGraph V) (hS : P S) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      P T ∧
      (∀ u v, u ≠ v → ¬ T.Adj u v →
        ¬ ∃ U : SimpleGraph V,
          (∀ x y, T.Adj x y → U.Adj x y) ∧
          P U ∧ U.Adj u v) := by
  obtain ⟨T,h1,h2,h3⟩ := S220WS.exists_maximal S P hS
  refine ⟨T,fun u v h => h1 h,h2,fun u v _ hn ⟨U,hU1,hU2,hU3⟩ => ?_⟩
  have := h3 U (fun x y h => hU1 x y h) hU2
  rw [this] at hU3; exact hn hU3
