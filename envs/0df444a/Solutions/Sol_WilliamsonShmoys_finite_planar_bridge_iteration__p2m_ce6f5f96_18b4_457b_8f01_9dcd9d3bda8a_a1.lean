-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_bridge_iteration__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:45:55.608982+00:00
-- url     : https://prove2.me/submissions/781d10aa-8015-4368-8a7b-9cc540e26bd0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

namespace S108WS

theorem le_of_le_card {V : Type} [Fintype V] {M N : SimpleGraph V} (h : M ≤ N)
    (hc : N.edgeSet.ncard ≤ M.edgeSet.ncard) : N = M := by
  have hs : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr h
  have := Set.eq_of_subset_of_ncard_le hs hc (Set.toFinite _)
  exact (SimpleGraph.edgeSet_inj.mp this).symm

theorem exists_max {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N → HasPlanarDrawingOn N → N.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      (∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun N => L ≤ N ∧ HasPlanarDrawingOn N)
  have hne : S.Nonempty := ⟨L, by simp [S, hL]⟩
  obtain ⟨M, hM, hmax⟩ := S.exists_max_image (fun N => N.edgeSet.ncard) hne
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hM hmax
  refine ⟨M, hM.1, hM.2, fun N h1 h2 => hmax N ⟨h1, h2⟩, fun N hN hP => ?_⟩
  exact le_of_le_card hN (hmax N ⟨le_trans hM.1 hN, hP⟩)

end S108WS

open S108WS
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K ≤ L ∧ K.edgeSet ⊂ L.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨M, h1, h2, h3, h4⟩ := exists_max G hG
  refine ⟨M, h1, ?_, h2, h3 G le_rfl hG⟩
  by_contra hc
  obtain ⟨L, hL1, hL2, hL3⟩ := hStep M h1 h2 hc
  have := h4 L hL1 hL3
  subst this
  exact hL2.ne rfl
