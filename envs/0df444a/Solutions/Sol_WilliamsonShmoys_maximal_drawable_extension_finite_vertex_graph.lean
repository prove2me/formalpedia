-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_finite_vertex_graph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:20:30.425163+00:00
-- url     : https://prove2.me/submissions/9a102342-42c6-4724-9bf2-44bf77ff1f6e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
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
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, G.edgeSet ⊆ W.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W.edgeSet ⊆ X.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn X → X.edgeSet ⊆ W.edgeSet := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen _ G hG
  refine ⟨H, SimpleGraph.edgeSet_mono h1, h2, fun X hX hXd => ?_⟩
  have : H ≤ X := SimpleGraph.edgeSet_subset_edgeSet.mp hX
  rw [h3 X this hXd]
