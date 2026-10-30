-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:45:52.218039+00:00
-- url     : https://prove2.me/submissions/048e5548-8b1d-4655-9476-e7c32c2d3f95

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
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K := by
  obtain ⟨M, h1, h2, h3, h4⟩ := exists_max N hN
  exact ⟨M, h1, h2, fun L hL hP => (h4 L hL hP).le⟩
