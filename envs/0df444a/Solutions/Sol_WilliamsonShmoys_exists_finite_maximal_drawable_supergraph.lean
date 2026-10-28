-- Prove2me | solution 1 for WilliamsonShmoys.exists_finite_maximal_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:08:49.268446+00:00
-- url     : https://prove2.me/submissions/b54b5a4c-82fd-403e-83f9-6d1f8bc40aa2

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
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ {u v}, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V,
        (∀ {u v}, S.Adj u v → T.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => WilliamsonShmoys.HasPlanarDrawingOn K) R hdraw
  exact ⟨H, fun h => h1 h, h2, fun T hT hTp => h3 T (fun _ _ h => hT h) hTp⟩
