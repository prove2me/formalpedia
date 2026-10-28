-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:43:50.125248+00:00
-- url     : https://prove2.me/submissions/e492d47b-5e8b-4d29-b971-dfd7cb61fa76

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


open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      X ≤ H ∧
      (X.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K = H) := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => WilliamsonShmoys.HasPlanarDrawingOn K) X hX
  exact ⟨H, h2, h1, by exact_mod_cast Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _),
    fun K hK hHK => h3 K hHK hK⟩
