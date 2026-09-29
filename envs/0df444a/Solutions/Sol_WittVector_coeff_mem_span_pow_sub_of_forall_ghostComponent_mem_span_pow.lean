-- Prove2me | solution 1 for WittVector.coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b1968121-1d85-557d-b09f-a2dc52d0b07e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow

set_option autoImplicit false

namespace S17PD

theorem ghostComponent_eq_sum {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S] (n : ℕ) (X : WittVector p S) :
    WittVector.ghostComponent n X = ∑ i ∈ Finset.range (n + 1), (p : S) ^ i * X.coeff i ^ p ^ (n - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]

theorem mem_span_pow_of_pow_mul_mem {S : Type*} [CommRing S] {p : ℕ} (hpR : (p : S) ∈ nonZeroDivisors S)
    {a : S} {K e : ℕ} (hKe : K ≤ e) (h : (p : S) ^ K * a ∈ Ideal.span {(p : S) ^ e}) :
    a ∈ Ideal.span {(p : S) ^ (e - K)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : S) ^ K * (b * (p : S) ^ (e - K) - a) = 0 := by
    rw [mul_sub, sub_eq_zero, ← hb, mul_comm ((p : S) ^ K), mul_assoc, ← pow_add, Nat.sub_add_cancel hKe]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 (pow_mem hpR K)).1 _ h0)

end S17PD

universe u

theorem solution
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ nonZeroDivisors S)
    (z : WittVector p S) (s M : ℕ)
    (hz : ∀ n : ℕ, n < M → WittVector.ghostComponent n z ∈ Ideal.span {(p : S) ^ s}) :
    ∀ j : ℕ, j < M → z.coeff j ∈ Ideal.span {(p : S) ^ (s - j)} := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hjM

    have hsum : ∑ i ∈ Finset.range j, (p : S) ^ i * z.coeff i ^ p ^ (j - i) ∈ Ideal.span {(p : S) ^ s} := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have hij : i < j := Finset.mem_range.1 hi
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (IH i hij (lt_trans hij hjM))
      rw [Ideal.mem_span_singleton, ← hb, mul_pow, ← pow_mul, mul_left_comm]
      refine Dvd.dvd.mul_left ?_ _
      rw [← pow_add]
      refine pow_dvd_pow _ ?_

      have he : 1 ≤ p ^ (j - i) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      rcases le_or_gt s i with hsi | hsi
      · omega
      · have : (s - i) * 1 ≤ (s - i) * p ^ (j - i) := Nat.mul_le_mul_left _ he
        omega

    have hrec : (p : S) ^ j * z.coeff j =
        WittVector.ghostComponent j z - ∑ i ∈ Finset.range j, (p : S) ^ i * z.coeff i ^ p ^ (j - i) := by
      rw [S17PD.ghostComponent_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
      ring
    have hmem : (p : S) ^ j * z.coeff j ∈ Ideal.span {(p : S) ^ s} := by
      rw [hrec]
      exact sub_mem (hz j hjM) hsum
    rcases le_or_gt j s with hjs | hjs
    · exact S17PD.mem_span_pow_of_pow_mul_mem hp hjs hmem
    · rw [Nat.sub_eq_zero_of_le hjs.le, pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top

end S_WittVector_coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow
end P2MW
export P2MW.S_WittVector_coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow (solution)
