-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_in_finite_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:26:10.848983+00:00
-- url     : https://prove2.me/submissions/948a87d9-a3b8-4d40-9c30-cb2012aa0a0c

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [Fintype (SimpleGraph V)]
    (S : Set (SimpleGraph V)) (hSfin : S.Finite) (hSne : S.Nonempty) :
    ∃ W, W ∈ S ∧
      ∀ X, X ∈ S →
        (∀ u v, W.Adj u v → X.Adj u v) →
        ∀ u v, X.Adj u v → W.Adj u v := by
  classical
  obtain ⟨W, hW, hmax⟩ := Set.exists_max_image S (fun K : SimpleGraph V => K.edgeSet.ncard) hSfin hSne
  refine ⟨W, hW, fun X hX hWX => ?_⟩
  have hle : W ≤ X := fun a b h => hWX a b h
  have heq : W.edgeSet = X.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hle) (hmax X hX) (Set.toFinite _)
  have : W = X := SimpleGraph.edgeSet_injective heq
  subst this; exact fun u v h => h
