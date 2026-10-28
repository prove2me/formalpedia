-- Prove2me | solution 1 for WernerExt.TwoSided.dual_dominance
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:30:34.33136+00:00
-- url     : https://prove2.me/submissions/7a67c891-eb5b-4ebb-8483-c221191db96e

import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

open Finset

theorem rev_tail_sum {d : ℕ} (f : Fin d → ℝ) (k : ℕ) (hk : k ≤ d) :
    ∑ i ∈ univ.filter (fun i : Fin d => i.val < k), f (Fin.rev i) +
      ∑ j ∈ univ.filter (fun j : Fin d => j.val < d - k), f j = ∑ j, f j := by
  have h1 : ∑ i ∈ univ.filter (fun i : Fin d => i.val < k), f (Fin.rev i) =
      ∑ j ∈ univ.filter (fun j : Fin d => ¬ (j.val < d - k)), f j := by
    apply Finset.sum_equiv Fin.revPerm
    · intro i
      simp only [mem_filter, mem_univ, true_and, Fin.revPerm_apply, Fin.val_rev]
      have := i.2
      omega
    · intro i _; simp
  rw [h1, add_comm]
  exact sum_filter_add_sum_filter_not _ _ _

theorem dual_dominance (d n M : ℕ) (hd : 2 ≤ d) (l m : DPart d n) (hlm : Dominates l.1 m.1)
    (hM : ∀ i : Fin d, l.1 i ≤ M ∧ m.1 i ≤ M) :
    Dominates (mDual M l.1) (mDual M m.1) := by
  intro k
  set k' := min k d with hk'
  have hF : univ.filter (fun i : Fin d => i.val < k) = univ.filter (fun i : Fin d => i.val < k') := by
    ext i; simp only [mem_filter, mem_univ, true_and]; have := i.2; omega
  rw [hF]
  have hcast : ∀ (x : Fin d → ℕ), (∀ i, x i ≤ M) →
      ((∑ i ∈ univ.filter (fun i : Fin d => i.val < k'), mDual M x i : ℕ) : ℝ) =
        ∑ i ∈ univ.filter (fun i : Fin d => i.val < k'), ((M : ℝ) - x (Fin.rev i)) := by
    intro x hx
    push_cast
    apply sum_congr rfl
    intro i _
    simp only [mDual]
    rw [Nat.cast_sub (hx _)]
  have hl := hcast l.1 (fun i => (hM i).1)
  have hm := hcast m.1 (fun i => (hM i).2)
  have hdom := hlm (d - k')
  have hdomR : ((∑ i ∈ univ.filter (fun i : Fin d => i.val < d - k'), m.1 i : ℕ) : ℝ) ≤
      ((∑ i ∈ univ.filter (fun i : Fin d => i.val < d - k'), l.1 i : ℕ) : ℝ) := by
    exact_mod_cast hdom
  push_cast at hdomR
  have tl := rev_tail_sum (fun i => (l.1 i : ℝ)) k' (min_le_right _ _)
  have tm := rev_tail_sum (fun i => (m.1 i : ℝ)) k' (min_le_right _ _)
  have sl : ∑ j, (l.1 j : ℝ) = n := by exact_mod_cast l.2.2
  have sm : ∑ j, (m.1 j : ℝ) = n := by exact_mod_cast m.2.2

  suffices h : ((∑ i ∈ univ.filter (fun i : Fin d => i.val < k'), mDual M m.1 i : ℕ) : ℝ) ≤
      ((∑ i ∈ univ.filter (fun i : Fin d => i.val < k'), mDual M l.1 i : ℕ) : ℝ) by
    exact_mod_cast h
  rw [hl, hm, sum_sub_distrib, sum_sub_distrib]
  linarith

end WernerExt.TwoSided


-- Platform entry point: restates the target verbatim.
namespace WernerExt.TwoSided

/-- SM Eq. (14), SM p. 3: taking the `M`-dual preserves dominance order: if `λ, μ ⊢_d n`,
`λ ⊵ μ` and `M` is at least the first rows of both, then `λ̄ ⊵ μ̄`. -/
theorem _root_.solution (d n M : ℕ) (hd : 2 ≤ d) (l m : DPart d n) (hlm : Dominates l.1 m.1)
    (hM : ∀ i : Fin d, l.1 i ≤ M ∧ m.1 i ≤ M) :
    Dominates (mDual M l.1) (mDual M m.1) := by
  apply @WernerExt.TwoSided.dual_dominance <;> assumption

end WernerExt.TwoSided
