-- Prove2me | solution 2 for WilliamsonShmoys.finite_maximal_drawable_supergraph_20261027
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:07:09.449775+00:00
-- url     : https://prove2.me/submissions/a437fcfd-5e53-4964-a214-e966be23297f

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
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    Exists fun Q : SimpleGraph V =>
      (forall {u v}, P.Adj u v -> Q.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn Q /\
      (forall R : SimpleGraph V,
        (forall {u v}, Q.Adj u v -> R.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn R -> R = Q) := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => WilliamsonShmoys.HasPlanarDrawingOn K) P hdraw
  exact ⟨H, fun h => h1 h, h2, fun R hR hRp => h3 R (fun _ _ h => hR h) hRp⟩
