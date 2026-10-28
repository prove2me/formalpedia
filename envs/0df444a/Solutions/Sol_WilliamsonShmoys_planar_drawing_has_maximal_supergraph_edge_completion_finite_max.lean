-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph_edge_completion_finite_max
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:25:30.674268+00:00
-- url     : https://prove2.me/submissions/942fd5f2-a359-42b0-af8e-84fec6e9cf22

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
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
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion W X := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => WilliamsonShmoys.HasPlanarDrawingOn K) W hW
  exact ⟨H, h2, fun u v h => h1 h, fun X hX hHX => h3 X (fun a b h => hHX a b h) hX⟩
