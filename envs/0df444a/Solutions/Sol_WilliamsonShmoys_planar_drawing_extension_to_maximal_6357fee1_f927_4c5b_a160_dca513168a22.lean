-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extension_to_maximal_6357fee1_f927_4c5b_a160_dca513168a22
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:15:58.972297+00:00
-- url     : https://prove2.me/submissions/c0dc0cfc-dea1-4a79-9b36-defe1b08a042

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem S195_gen
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hP : P N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun K => N ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨N, by simp [S, hP]⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have h1 := hmax K ⟨hH.1.trans hHK, hK⟩
  have heq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHK) h1 (Set.toFinite _)
  exact (SimpleGraph.edgeSet_injective heq).symm


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (H <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (H.edgeSet.ncard <= K.edgeSet.ncard)
          (forall L : SimpleGraph V, K <= L ->
            WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K))) := by
  obtain ⟨K, h1, h2, h3⟩ := S195_gen _ H hH
  exact ⟨K, h1, h2, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _),
    fun L hKL hL => (h3 L hKL hL).le⟩
