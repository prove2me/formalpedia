-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:00:48.350237+00:00
-- url     : https://prove2.me/submissions/0ba63add-5cfe-4547-a57a-256575211408

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

open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ P : SimpleGraph V, G ≤ P ∧ HasPlanarDrawingOn P ∧ ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P := by
  obtain ⟨H,h1,h2,h3⟩ := S220WS.exists_maximal G _ hG
  exact ⟨H,h1,h2,fun Q a b => (h3 Q a b).le⟩
