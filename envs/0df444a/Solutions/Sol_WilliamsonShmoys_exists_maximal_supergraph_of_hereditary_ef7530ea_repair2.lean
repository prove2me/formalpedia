-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_hereditary_ef7530ea_repair2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:13:55.947625+00:00
-- url     : https://prove2.me/submissions/457db75b-08f8-400c-b3f4-fb09e1cd64e5

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ G H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) → P H → P G)
    (N : SimpleGraph V) (hN : P N) :
    ∃ M : SimpleGraph V,
      (∀ u v, N.Adj u v → M.Adj u v) ∧
      (P M ∧ ∀ M' : SimpleGraph V,
        (∀ u v, M.Adj u v → M'.Adj u v) → P M' →
        ∀ u v, M'.Adj u v → M.Adj u v) := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun K => N ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨N, by simp [S, hN]⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, fun u v h => hH.1 h, hH.2, ?_⟩
  intro K hHK hK
  have hle : H ≤ K := fun u v h => hHK u v h
  have h1 := hmax K ⟨hH.1.trans hle, hK⟩
  have heq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hle) h1 (Set.toFinite _)
  have : K = H := (SimpleGraph.edgeSet_injective heq).symm
  intro u v h; rw [← this]; exact h
