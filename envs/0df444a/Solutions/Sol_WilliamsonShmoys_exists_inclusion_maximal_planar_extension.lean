-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:00:42.524734+00:00
-- url     : https://prove2.me/submissions/5df364c8-2b63-4b78-9902-9d51bd57d265

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

set_option autoImplicit false
theorem S191EY_gen
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

open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ IsMaximalPlanarOn K := by
  obtain ⟨K, h1, h2, h3⟩ := S191EY_gen _ H hHplanar
  exact ⟨K, h1, h2, h3⟩
