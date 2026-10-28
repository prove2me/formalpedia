-- Prove2me | solution 1 for TailOptCaching.ETLRU.next_turn_expected_TEL
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:02:35.552634+00:00
-- url     : https://prove2.me/submissions/05ddb308-2264-493f-881e-1e3f24ae817b

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

open TailOptCaching.ETLRU in
theorem solution (P : Params) (z : State) (hz : WellFormed P z) (d : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    arrivalExp P (decay d z) (fun θ q _ => stageCost P (decay d z) θ q) *
        ENNReal.ofReal (P.lamConv + d * ∑ i ∈ Finset.range z.n, z.lam i) =
      ENNReal.ofReal d * nextTEL P z +
        ENNReal.ofReal P.lamConv * ∑' Q : ℕ, P.Qlaw z.n Q * ENNReal.ofReal ((Q : ℝ) - P.ξ) := by
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hz
  have hsum : 0 ≤ ∑ i ∈ Finset.range z.n, z.lam i :=
    Finset.sum_nonneg (fun i hi => (hw1 i (Finset.mem_range.mp hi)).1.le)
  have hS : 0 < P.lamConv + d * ∑ i ∈ Finset.range z.n, z.lam i := by
    have := P.lamConv_pos
    nlinarith [mul_nonneg hd.le hsum]
  obtain ⟨S, hSdef⟩ : ∃ S, S = P.lamConv + d * ∑ i ∈ Finset.range z.n, z.lam i := ⟨_, rfl⟩
  rw [← hSdef] at hS ⊢
  have hden : P.lamConv + ∑ i ∈ Finset.range z.n, d * z.lam i = S := by
    rw [hSdef, Finset.mul_sum]
  have key : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x / S) * ENNReal.ofReal S = ENNReal.ofReal x := by
    intro x hx
    rw [← ENNReal.ofReal_mul (div_nonneg hx hS.le), div_mul_cancel₀ _ hS.ne']
  have hn := hw2 z.n le_rfl
  unfold arrivalExp
  rw [Finset.sum_range_succ, add_mul, Finset.sum_mul]
  congr 1
  · unfold nextTEL
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ hθ
    have hθ' : θ < z.n := Finset.mem_range.mp hθ
    simp only [arrivalProb, decay, stageCost, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
      hθ', ite_true, hden]
    rw [mul_right_comm, key _ (mul_nonneg hd.le (hw1 θ hθ').1.le), ENNReal.ofReal_mul hd.le,
      mul_assoc]
  · simp only [arrivalProb, decay, stageCost, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
      lt_self_iff_false, ite_true, ite_false, hden, hn.2.1, hn.2.2, Nat.cast_zero, zero_add,
      sub_zero]
    try rw [if_neg (lt_irrefl _)]
    try rw [if_pos rfl]
    rw [mul_right_comm, key _ P.lamConv_pos.le]
