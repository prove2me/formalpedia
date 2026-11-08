-- Prove2me | solution 1 for VehShare.MultiNet.chu_vandermonde_real
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:21:46.811424+00:00
-- url     : https://prove2.me/submissions/b8d025bf-d44b-4950-8650-9ea66dd968a2

import Mathlib

theorem solution (T T₁ : ℝ) (K : ℕ) :
    ∑ K₁ ∈ Finset.range (K + 1),
        Ring.choose ((K : ℝ) + T - K₁ - T₁ - 1) (K - K₁) * Ring.choose (T₁ + K₁ - 1) K₁ =
      Ring.choose ((K : ℝ) + T - 1) K := by
  have hs : ∀ (r : ℝ) (n : ℕ), Ring.choose (r + n - 1) n =
      ((((n : ℤ).negOnePow : ℤˣ) : ℤ) : ℝ) * Ring.choose (-r) n := by
    intro r n
    rw [Ring.choose_neg, Units.smul_def, zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  have hterm : ∀ K₁ ∈ Finset.range (K + 1),
      Ring.choose ((K : ℝ) + T - K₁ - T₁ - 1) (K - K₁) * Ring.choose (T₁ + K₁ - 1) K₁ =
        ((((K : ℤ).negOnePow : ℤˣ) : ℤ) : ℝ) *
          (Ring.choose (-T₁) K₁ * Ring.choose (-(T - T₁)) (K - K₁)) := by
    intro K₁ hK₁
    have hle : K₁ ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hK₁)
    have e : (K : ℝ) + T - K₁ - T₁ - 1 = (T - T₁) + ((K - K₁ : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hle]
      ring
    rw [e, hs, hs]
    have hu : ((((K - K₁ : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) * ((((K₁ : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) =
        (((K : ℤ).negOnePow : ℤˣ) : ℤ) := by
      rw [← Units.val_mul, ← Int.negOnePow_add]
      congr 2
      omega
    have hu' : ((((((K - K₁ : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : ℝ)) *
        ((((((K₁ : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : ℝ)) = ((((K : ℤ).negOnePow : ℤˣ) : ℤ) : ℝ) := by
      rw [← Int.cast_mul, hu]
    rw [← hu']
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hv : ∑ k ∈ Finset.range (K + 1), Ring.choose (-T₁) k * Ring.choose (-(T - T₁)) (K - k) =
      Ring.choose (-T) K := by
    have h2 := Ring.add_choose_eq (R := ℝ) (r := -T₁) (s := -(T - T₁)) K (Commute.all _ _)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      show -T₁ + -(T - T₁) = -T by ring] at h2
    exact h2.symm
  rw [hv, show (K : ℝ) + T - 1 = T + K - 1 by ring, hs]
