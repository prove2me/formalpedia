-- Prove2me | solution 1 for TwoAgentSched.seqC_feasible
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T02:43:59.711189+00:00
-- url     : https://prove2.me/submissions/b259bc54-c2c3-45e2-a5dd-77e1b83fcd0d

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible

open TwoAgentSched

namespace TwoAgentSched.SeqCProof

variable {ι : Type} [DecidableEq ι]

lemma seqC_cons_self (p : ι → ℝ) (a : ι) (rest : List ι) :
    seqC p (a :: rest) a = p a := by
  simp [seqC]

lemma seqC_cons_ne (p : ι → ℝ) (a j : ι) (rest : List ι) (h : j ≠ a) :
    seqC p (a :: rest) j = p a + seqC p rest j := by
  simp only [seqC]
  rw [List.idxOf_cons_ne rest (Ne.symm h)]
  simp [List.take_succ_cons, List.map_cons, List.sum_cons]

lemma seqC_mem_nonneg (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : List ι) {j : ι}
    (hj : j ∈ σ) : p j ≤ seqC p σ j := by
  induction σ with
  | nil => simp at hj
  | cons a rest ih =>
      by_cases h : j = a
      · subst h
        rw [seqC_cons_self]
      · rw [seqC_cons_ne p a j rest h]
        have hj' : j ∈ rest := by simpa [h] using hj
        have := ih hj'
        have := hp a
        linarith

lemma seqC_add_le (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : List ι) {i j : ι}
    (hi : i ∈ σ) (hj : j ∈ σ) (hij : σ.idxOf i < σ.idxOf j) :
    seqC p σ i + p j ≤ seqC p σ j := by
  induction σ with
  | nil => simp at hi
  | cons a rest ih =>
      by_cases hia : i = a
      · rw [hia]
        have hja : j ≠ a := by
          intro hja
          rw [hja] at hij
          rw [List.idxOf_cons_self] at hij
          exact Nat.not_lt_zero _ hij
        rw [seqC_cons_self, seqC_cons_ne p a j rest hja]
        have hj' : j ∈ rest := by simpa [hja] using hj
        have := seqC_mem_nonneg p hp rest hj'
        linarith
      · have hja : j ≠ a := by
          intro hja
          rw [hja] at hij
          rw [List.idxOf_cons_self] at hij
          rw [List.idxOf_cons_ne rest (Ne.symm hia)] at hij
          exact Nat.not_lt_zero _ hij
        have hi' : i ∈ rest := by simpa [hia] using hi
        have hj' : j ∈ rest := by simpa [hja] using hj
        rw [seqC_cons_ne p a i rest hia, seqC_cons_ne p a j rest hja]
        have hidx : rest.idxOf i < rest.idxOf j := by
          rw [List.idxOf_cons_ne rest (Ne.symm hia),
            List.idxOf_cons_ne rest (Ne.symm hja)] at hij
          omega
        have := ih hi' hj' hidx
        linarith

end TwoAgentSched.SeqCProof

/-- Starting every job when its predecessor in the sequence completes gives a feasible
schedule. -/
theorem solution {ι : Type} [DecidableEq ι] (p : ι → ℝ) (σ : List ι)
    (hp : ∀ j, 0 ≤ p j) (hσ : IsSeq σ) :
    Feasible p (fun j => seqC p σ j - p j) := by
  constructor
  · intro j
    have hj : j ∈ σ := hσ.2 j
    have h := TwoAgentSched.SeqCProof.seqC_mem_nonneg p hp σ hj
    linarith
  · intro i j hij
    have hi : i ∈ σ := hσ.2 i
    have hj : j ∈ σ := hσ.2 j
    have hne : σ.idxOf i ≠ σ.idxOf j := by
      intro h
      exact hij (List.idxOf_inj hi |>.mp h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have h := TwoAgentSched.SeqCProof.seqC_add_le p hp σ hi hj hlt
      rw [sub_add_cancel, le_sub_iff_add_le]
      exact h
    · right
      have h := TwoAgentSched.SeqCProof.seqC_add_le p hp σ hj hi hgt
      rw [sub_add_cancel, le_sub_iff_add_le]
      exact h
