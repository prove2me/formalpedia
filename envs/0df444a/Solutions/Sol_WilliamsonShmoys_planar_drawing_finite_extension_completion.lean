-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_extension_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:15:48.589418+00:00
-- url     : https://prove2.me/submissions/9a454f22-209e-44f2-87d3-a9be4d7afaf2

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
    (L : SimpleGraph V) (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hstep : ∀ K : SimpleGraph V,
      L.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ H : SimpleGraph V,
        K.edgeSet ⊆ H.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (∀ u v, H.Adj u v → K.Adj u v ∨ ¬ K.Reachable u v) ∧
        (∃ u v, H.Adj u v ∧ ¬ K.Reachable u v)) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨M, hLM, hM, hmax⟩ := S195_gen _ L hLdraw
  have hLM' : L.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hLM
  refine ⟨M, hLM', ?_, hM⟩
  by_contra hc
  obtain ⟨H, hMH, hH, -, u, v, huv, hnr⟩ := hstep M hLM' hM hc
  have hle : M ≤ H := fun a b hab => (SimpleGraph.mem_edgeSet _).1 (hMH ((SimpleGraph.mem_edgeSet _).2 hab))
  have := hmax H hle hH
  subst this
  exact hnr huv.reachable
