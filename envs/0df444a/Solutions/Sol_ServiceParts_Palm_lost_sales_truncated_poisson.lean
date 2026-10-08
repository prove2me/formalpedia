-- Prove2me | solution 1 for ServiceParts.Palm.lost_sales_truncated_poisson
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:20:22.857379+00:00
-- url     : https://prove2.me/submissions/12db6a68-e623-4057-a8f1-5ace7f763eb7

import Mathlib
import Definitions.Def_ServiceParts_Palm_LostSalesBalance

set_option autoImplicit false

namespace LSTP8cd3

open ServiceParts.Palm

lemma bal_iff (lam β : ℝ) (s : ℕ) (π : ℕ → ℝ) :
    LostSalesBalance lam β s π ↔ ∀ j, j < s → ((j:ℝ)+1)*β*π (j+1) = lam * π j := by
  constructor
  · intro h j
    induction j with
    | zero =>
      intro hj
      have := h 0 (le_of_lt hj)
      simp only [hj, if_true, lt_irrefl, if_false, Nat.cast_zero, zero_mul, add_zero,
        zero_add, one_mul] at this
      simp only [Nat.cast_zero, zero_add, one_mul]
      linarith
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have := h (k+1) (le_of_lt hk)
      simp only [hk, if_true, Nat.succ_pos, Nat.add_sub_cancel] at this
      push_cast at this ⊢
      linarith
  · intro H j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · by_cases h0 : 0 < s
      · have := H 0 h0
        simp only [h0, if_true, lt_irrefl, if_false, Nat.cast_zero, zero_mul, add_zero,
          zero_add, one_mul]
        simp only [Nat.cast_zero, zero_add, one_mul] at this
        linarith
      · simp [h0]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j-1, by omega⟩
      have h1 := H k (by omega)
      by_cases hs : k + 1 < s
      · have h2 := H (k+1) hs
        simp only [hs, if_true, Nat.succ_pos, Nat.add_sub_cancel]
        push_cast at h1 h2 ⊢
        linarith
      · simp only [hs, if_false, Nat.succ_pos, if_true, Nat.add_sub_cancel, add_zero, zero_add]
        push_cast at h1 ⊢
        linarith

lemma q_succ (r : ℝ) (n : ℕ) :
    r^(n+1) / ((n+1).factorial : ℝ) * ((n:ℝ)+1) = r^n / (n.factorial:ℝ) * r := by
  rw [Nat.factorial_succ]; push_cast
  have : (n.factorial:ℝ) ≠ 0 := by positivity
  field_simp; ring

end LSTP8cd3

open LSTP8cd3 in
open ServiceParts.Palm in
theorem solution (lam β : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (s : ℕ)
    (π : ℕ → ℝ) :
    (LostSalesBalance lam β s π ∧ ∑ j ∈ Finset.range (s + 1), π j = 1) ↔
      ∀ x, x ≤ s →
        π x = (Real.exp (-(lam / β)) * (lam / β) ^ x / (Nat.factorial x : ℝ)) /
          ∑ n ∈ Finset.range (s + 1),
            Real.exp (-(lam / β)) * (lam / β) ^ n / (Nat.factorial n : ℝ) := by
  rw [bal_iff]
  set r := lam / β with hr
  have hlamr : lam = r * β := by rw [hr]; field_simp
  have hrpos : 0 < r := div_pos hlam hβ
  have hE : Real.exp (-r) ≠ 0 := (Real.exp_pos _).ne'
  have key : ∀ x : ℕ, Real.exp (-r) * r ^ x / (x.factorial : ℝ) /
      ∑ n ∈ Finset.range (s + 1), Real.exp (-r) * r ^ n / (n.factorial : ℝ) =
      (r ^ x / x.factorial) / ∑ n ∈ Finset.range (s + 1), r ^ n / (n.factorial : ℝ) := by
    intro x
    have : ∑ n ∈ Finset.range (s + 1), Real.exp (-r) * r ^ n / (n.factorial : ℝ) =
        Real.exp (-r) * ∑ n ∈ Finset.range (s + 1), r ^ n / (n.factorial : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [this, mul_div_assoc, mul_div_mul_left _ _ hE]
  simp only [key]
  set T := ∑ n ∈ Finset.range (s + 1), r ^ n / (n.factorial : ℝ) with hT
  have hTpos : 0 < T := by
    apply Finset.sum_pos (fun n _ => by positivity) (by simp)
  constructor
  · rintro ⟨H, hsum⟩
    have hform : ∀ x, x ≤ s → π x = π 0 * (r ^ x / (x.factorial : ℝ)) := by
      intro x
      induction x with
      | zero => intro; simp
      | succ k ih =>
        intro hk
        have h1 := H k (by omega)
        have h2 := ih (by omega)
        have hq := q_succ r k
        have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
        apply mul_left_cancel₀ (mul_ne_zero hk1 hβ.ne')
        linear_combination h1 + lam * h2 + π 0 * (r ^ k / (k.factorial : ℝ)) * hlamr
          - β * π 0 * hq
    have hsum' : π 0 * T = 1 := by
      rw [← hsum, hT, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => (hform j (by simp at hj; omega)).symm)
    intro x hx
    rw [hform x hx, eq_div_iff hTpos.ne', mul_right_comm, hsum', one_mul]
  · intro H
    have hsum : ∑ j ∈ Finset.range (s + 1), π j = 1 := by
      rw [Finset.sum_congr rfl (fun j hj => H j (by simp at hj; omega)), ← Finset.sum_div]
      exact div_self hTpos.ne'
    refine ⟨fun j hj => ?_, hsum⟩
    rw [H j hj.le, H (j+1) (by omega), hlamr]
    have hq := q_succ r j
    rw [show ((j:ℝ)+1) * β * (r ^ (j+1) / ((j+1).factorial : ℝ) / T)
        = β * (r ^ (j+1) / ((j+1).factorial : ℝ) * ((j:ℝ)+1)) / T by ring, hq]
    ring
