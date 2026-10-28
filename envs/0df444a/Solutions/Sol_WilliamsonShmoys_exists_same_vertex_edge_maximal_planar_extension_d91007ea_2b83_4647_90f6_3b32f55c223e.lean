-- Prove2me | solution 1 for WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension_d91007ea_2b83_4647_90f6_3b32f55c223e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:24:15.176258+00:00
-- url     : https://prove2.me/submissions/a60f1675-2c95-4498-abf4-ab55677583f1

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
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ M : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        ∀ ⦃u v⦄, M.Adj u v → K.Adj u v) := by
  obtain ⟨K, h1, h2, h3⟩ := S195_gen _ L hL
  refine ⟨K, fun u v h => h1 h, h2, fun M hKM hM u v h => ?_⟩
  have := h3 M (fun a b hab => hKM hab) hM
  subst this
  exact h
