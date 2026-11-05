-- Prove2me | solution 1 for TenChallenges.bounded_order_graphs_zero_wqo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:21.344146+00:00
-- url     : https://prove2.me/submissions/f8025fc2-a4cb-4f87-9a61-b1683fb03cac

import Definitions.Def_TenChallenges_Challenge_06
import Mathlib.Data.Fintype.Pigeonhole

universe u

theorem alpha_zero_iff {Q : Type u} (r : Q → Q → Prop) :
    IsAlphaWQO r 0 ↔ IsWQO r := by
  unfold IsAlphaWQO IsWQO
  simp only [leStar, Ordinal.limitRecOn_zero]
  constructor
  · intro h f
    obtain ⟨i, j, hij, hr⟩ := h (fun n => cast (VStar_zero Q).symm (f n))
    exact ⟨i, j, hij, by simpa using hr⟩
  · intro h f
    exact h (fun n => cast (VStar_zero Q) (f n))

/-- Every finite reflexive relation satisfies the level-zero WQO assertion. -/
theorem finite_reflexive_alpha_zero {Q : Type u} [Finite Q] (r : Q → Q → Prop)
    (hrefl : ∀ q, r q q) : IsAlphaWQO r 0 := by
  rw [alpha_zero_iff]
  intro f
  obtain ⟨i, j, heq, hne⟩ : ∃ i j : ℕ, f i = f j ∧ i ≠ j := by
    simpa [Function.Injective] using not_injective_infinite_finite f
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, by simpa only [heq] using hrefl (f i)⟩
  · exact ⟨j, i, h, by simpa only [heq] using hrefl (f j)⟩

/-- Finite graphs of bounded order are level-zero well-quasi-ordered by minors. -/
theorem solution (N : ℕ) :
    IsAlphaWQO (fun G H : (Σ n : Fin (N + 1), SimpleGraph (Fin n.val)) =>
      Nonempty (SimpleGraph.Minor G.2 H.2)) 0 := by
  classical
  apply finite_reflexive_alpha_zero
  intro G
  refine ⟨{
    branchSet := fun v => {v}
    pairwise_disjoint_branchSet := ?_
    connectedOn_branchSet := ?_
    exists_mem_branchSet_of_adj := ?_
  }⟩
  · intro v w hvw
    exact Set.disjoint_singleton.mpr hvw
  · intro v
    exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
  · intro v w hvw
    exact ⟨v, rfl, w, rfl, hvw⟩
