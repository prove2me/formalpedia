-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_drawing_on_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:24:08.245369+00:00
-- url     : https://prove2.me/submissions/f8e2b5b3-1ed8-4a5d-817c-8a8dcd37dd4c

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
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      (∀ W : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn W →
        (∀ u v, U.Adj u v → W.Adj u v) → W = U) := by
  obtain ⟨U, h1, h2, h3⟩ := S195_gen _ T hT
  exact ⟨U, h2, fun u v h => h1 h, fun W hW hUW => h3 W (fun u v h => hUW u v h) hW⟩
