-- Prove2me | solution 1 for WilliamsonShmoys.drawable_planar_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:20:27.97907+00:00
-- url     : https://prove2.me/submissions/7d3edf22-229b-40f5-bd45-15208d89a462

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


open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, HasPlanarDrawingOn W ∧
      (∀ u v, G.Adj u v → W.Adj u v) ∧
      (∀ X : SimpleGraph V, HasPlanarDrawingOn X →
        (∀ u v, W.Adj u v → X.Adj u v) →
        ∀ u v, X.Adj u v → W.Adj u v) := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen _ G hG
  refine ⟨H, h2, fun u v h => h1 h, fun X hX hWX u v huv => ?_⟩
  have : H ≤ X := fun a b h => hWX a b h
  rw [← h3 X this hX]; exact huv
