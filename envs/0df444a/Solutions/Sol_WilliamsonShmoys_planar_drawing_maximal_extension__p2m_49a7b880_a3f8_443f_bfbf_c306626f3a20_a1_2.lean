-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:45:50.87528+00:00
-- url     : https://prove2.me/submissions/b14dabfb-c9c5-4fb8-9cec-677b4f063d71

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
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ L := by
  obtain ⟨M, h1, h2, h3, h4⟩ := exists_max K hK
  exact ⟨M, h1, h2, fun N hN hP => (h4 N hN hP).le⟩
