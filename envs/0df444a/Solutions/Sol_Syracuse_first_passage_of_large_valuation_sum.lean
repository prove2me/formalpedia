-- Prove2me | solution 1 for Syracuse.first_passage_of_large_valuation_sum
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:36.164605+00:00
-- url     : https://prove2.me/submissions/f32769ce-d513-470f-9da9-cddad96698b7

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

private theorem syracuse_valuation_bound_of_prefix_above (b n k : ℕ)
    (hstay : ∀ j ≤ k, b ≤ syracuseStep^[j] n) :
    b^k * 2^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) * b
      ≤ (3*b+1)^k * n := by
  let A (j : ℕ) := (Finset.range j).sum fun i => (3*syracuseStep^[i] n+1).factorization 2
  have hprod (j : ℕ) (hj : j ≤ k) : b^j * 2^(A j) * syracuseStep^[j] n ≤ (3*b+1)^j * n := by
    induction j with
    | zero => simp [A]
    | succ j ih =>
      have hjk : j ≤ k := (Nat.le_succ j).trans hj
      let x := syracuseStep^[j] n
      let y := syracuseStep x
      let a := (3*x+1).factorization 2
      have hsum : A (j+1) = A j + a := Finset.sum_range_succ _ _
      have hy : 2^a * y = 3*x+1 := Nat.ordProj_mul_ordCompl_eq_self _ _
      have hlin : b * (3*x+1) ≤ (3*b+1)*x := calc
        b * (3*x+1) = 3*b*x+b := by ring
        _ ≤ 3*b*x+x := Nat.add_le_add_left (hstay j hjk) _
        _ = (3*b+1)*x := by ring
      rw [Function.iterate_succ_apply', hsum, pow_succ b j, pow_succ (3*b+1) j, pow_add 2 (A j) a]
      change b^j*b*(2^(A j)*2^a)*y ≤ (3*b+1)^j*(3*b+1)*n
      calc
        _ = b^j*2^(A j)*(b*(2^a*y)) := by ring
        _ = b^j*2^(A j)*(b*(3*x+1)) := by rw [hy]
        _ ≤ b^j*2^(A j)*((3*b+1)*x) := Nat.mul_le_mul_left _ hlin
        _ = (b^j*2^(A j)*x)*(3*b+1) := by ring
        _ ≤ ((3*b+1)^j*n)*(3*b+1) := Nat.mul_le_mul_right _ (ih hjk)
        _ = (3*b+1)^j*(3*b+1)*n := by ring
  exact (Nat.mul_le_mul_left (b^k * 2^(A k)) (hstay k le_rfl)).trans (hprod k le_rfl)

theorem solution (b n k : ℕ)
    (h : (3*b+1)^k * n <
      b^k * 2^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) * b) :
    ∃ j ≤ k, syracuseStep^[j] n < b := by
  by_contra hex
  have hstay (j : ℕ) (hj : j ≤ k) : b ≤ syracuseStep^[j] n :=
    Nat.le_of_not_gt (fun hlt => hex ⟨j, hj, hlt⟩)
  exact (Nat.not_lt_of_ge (syracuse_valuation_bound_of_prefix_above b n k hstay)) h
