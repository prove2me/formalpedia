-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_3d83e52d_d7f3_4064_9901_f4d565126921
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:20:38.713521+00:00
-- url     : https://prove2.me/submissions/6616ce16-bf4b-42f6-b4ee-3ad2f0ac4223

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
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X ≤ Y →
        WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X :=
  S195_gen _ W hW
