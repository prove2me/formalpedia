-- Prove2me | solution 1 for QuaternionAlgebra.exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/02b147d1-9b20-53b5-b196-da2ad1ec19e8

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

namespace MinkowskiSerreQuaternionRigidity

def lucasU (t m : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (k + 2) => t * lucasU t m (k + 1) - m * lucasU t m k

theorem lucasU_zero (t m : ℚ) : lucasU t m 0 = 0 := rfl

theorem lucasU_one (t m : ℚ) : lucasU t m 1 = 1 := rfl

theorem lucasU_add_two (t m : ℚ) (k : ℕ) :
    lucasU t m (k + 1 + 1) = t * lucasU t m (k + 1) - m * lucasU t m k := rfl

theorem pow_succ_eq_lucasU {A : Type*} [Ring A] [Algebra ℚ A] (t m : ℚ) (x : A)
    (hx : x * x = t • x - m • (1 : A)) (k : ℕ) :
    x ^ (k + 1) = lucasU t m (k + 1) • x - (m * lucasU t m k) • (1 : A) := by
  induction k with
  | zero => simp [lucasU_zero, lucasU_one]
  | succ k ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hx, lucasU_add_two]
    module

theorem exists_int_sq_eq_mul_of_forall_root_pow_eq (t m r : ℚ) (hD : t ^ 2 < 4 * m)
    (n : ℕ) (hn : 0 < n)
    (h : ∀ w : ℂ, w * w = (t : ℂ) * w - (m : ℂ) → w ^ n = (r : ℂ)) :
    ∃ k : ℤ, 0 ≤ k ∧ k < 4 ∧ t ^ 2 = k * m := by
  have hm : 0 < m := by nlinarith [sq_nonneg t]
  have hDR : (0 : ℝ) < 4 * (m : ℝ) - (t : ℝ) ^ 2 := by
    have : ((t : ℝ)) ^ 2 < 4 * (m : ℝ) := by exact_mod_cast hD
    linarith
  set d : ℝ := Real.sqrt (4 * (m : ℝ) - (t : ℝ) ^ 2) with hd
  have hd2R : d ^ 2 = 4 * (m : ℝ) - (t : ℝ) ^ 2 := Real.sq_sqrt hDR.le
  have hd2 : (d : ℂ) ^ 2 = 4 * (m : ℂ) - (t : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, hd2R]
    push_cast
    ring
  set w : ℂ := ((t : ℂ) + (d : ℂ) * Complex.I) / 2 with hw
  set w' : ℂ := ((t : ℂ) - (d : ℂ) * Complex.I) / 2 with hw'
  have hw2 : w * w = (t : ℂ) * w - (m : ℂ) := by
    rw [hw]
    linear_combination ((d : ℂ) ^ 2 / 4) * Complex.I_sq + (-(1 : ℂ) / 4) * hd2
  have hw'2 : w' * w' = (t : ℂ) * w' - (m : ℂ) := by
    rw [hw']
    linear_combination ((d : ℂ) ^ 2 / 4) * Complex.I_sq + (-(1 : ℂ) / 4) * hd2
  have hww' : w * w' = (m : ℂ) := by
    rw [hw, hw']
    linear_combination (-(d : ℂ) ^ 2 / 4) * Complex.I_sq + ((1 : ℂ) / 4) * hd2
  have hadd : w + w' = (t : ℂ) := by
    rw [hw, hw']
    ring
  have hn1 : w ^ n = (r : ℂ) := h w hw2
  have hn2 : w' ^ n = (r : ℂ) := h w' hw'2
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw0 : w ≠ 0 := by
    intro h0
    apply hm0
    rw [← hww', h0, zero_mul]
  have hw'0 : w' ≠ 0 := by
    intro h0
    apply hm0
    rw [← hww', h0, mul_zero]
  have hr0 : (r : ℂ) ≠ 0 := by
    rw [← hn1]
    exact pow_ne_zero _ hw0
  set u : ℂ := w / w' with hu
  have hun : u ^ n = 1 := by
    rw [hu, div_pow, hn1, hn2, div_self hr0]
  have hu_int : IsIntegral ℤ u :=
    IsIntegral.of_pow hn (by rw [hun]; exact isIntegral_one)
  have hui_int : IsIntegral ℤ u⁻¹ :=
    IsIntegral.of_pow hn (by rw [inv_pow, hun, inv_one]; exact isIntegral_one)
  have hsq : w * w + w' * w' = (t : ℂ) ^ 2 - 2 * (m : ℂ) := by
    linear_combination (w + w' + (t : ℂ)) * hadd - 2 * hww'
  have hsum : u + u⁻¹ = ((t ^ 2 / m - 2 : ℚ) : ℂ) := by
    rw [hu, inv_div, div_add_div _ _ hw'0 hw0, hsq, mul_comm w' w, hww']
    push_cast
    field_simp
  obtain ⟨K, hK⟩ := (hu_int.add hui_int).exists_int_iff_exists_rat.mp ⟨t ^ 2 / m - 2, hsum⟩
  have hq : (t ^ 2 / m - 2 : ℚ) = (K : ℚ) := by
    have h1 : ((t ^ 2 / m - 2 : ℚ) : ℂ) = ((K : ℚ) : ℂ) := by
      rw [← hsum, hK]
      push_cast
      rfl
    exact_mod_cast h1
  have hk : t ^ 2 = ((K + 2 : ℤ) : ℚ) * m := by
    push_cast
    field_simp at hq
    linear_combination hq
  refine ⟨K + 2, ?_, ?_, hk⟩
  · by_contra hneg
    push Not at hneg
    have h1 : ((K + 2 : ℤ) : ℚ) < 0 := by exact_mod_cast hneg
    nlinarith [sq_nonneg t]
  · by_contra hge
    push Not at hge
    have h1 : (4 : ℚ) ≤ ((K + 2 : ℤ) : ℚ) := by exact_mod_cast hge
    nlinarith

theorem mul_self_eq_trd_smul_sub_nrd_smul {a b : ℚ} (x : ℍ[ℚ, a, b]) :
    x * x = trd x • x - nrd x • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp [trd, nrd] <;> ring

theorem trd_sq_lt_four_mul_nrd {a b : ℚ} (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b])
    (hx : ¬ (x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0)) : (trd x) ^ 2 < 4 * nrd x := by
  simp only [trd, nrd]
  have h1 : 0 ≤ -a * x.imI ^ 2 := mul_nonneg (neg_nonneg.mpr ha.le) (sq_nonneg _)
  have h2 : 0 ≤ -b * x.imJ ^ 2 := mul_nonneg (neg_nonneg.mpr hb.le) (sq_nonneg _)
  have h3 : 0 ≤ a * b * x.imK ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
  by_cases hI : x.imI = 0
  · by_cases hJ : x.imJ = 0
    · have hK : x.imK ≠ 0 := fun hK => hx ⟨hI, hJ, hK⟩
      have hK2 : 0 < x.imK ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hK))
      have : 0 < a * b * x.imK ^ 2 := mul_pos (mul_pos_of_neg_of_neg ha hb) hK2
      nlinarith
    · have hJ2 : 0 < x.imJ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hJ))
      have : 0 < -b * x.imJ ^ 2 := mul_pos (neg_pos.mpr hb) hJ2
      nlinarith
  · have hI2 : 0 < x.imI ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hI))
    have : 0 < -a * x.imI ^ 2 := mul_pos (neg_pos.mpr ha) hI2
    nlinarith

theorem rigidity {a b : ℚ} (ha : a < 0) (hb : b < 0) (L : Submodule ℤ ℍ[ℚ, a, b])
    (hL : IsOrder L) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (s : ℕ) (hs : ¬ ℓ ∣ s)
    (γ y : ℍ[ℚ, a, b]) (hy : (s : ℚ) • y ∈ L) (hγ : γ = 1 + (ℓ : ℚ) • y)
    (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : γ ^ n = c • (1 : ℍ[ℚ, a, b])) :
    ∃ c' : ℚ, γ = c' • (1 : ℍ[ℚ, a, b]) := by

  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (dvd_zero ℓ)
  have hs0Q : (s : ℚ) ≠ 0 := by exact_mod_cast hs0

  obtain ⟨⟨T, M, hT, hM⟩, -⟩ := hL.exists_int_trd_eq_and_nrd_eq hy

  set β : ℍ[ℚ, a, b] := (s : ℚ) • γ with hβ
  have hγβ : γ = (s : ℚ)⁻¹ • β := by rw [hβ, inv_smul_smul₀ hs0Q]

  by_cases hcen : β.imI = 0 ∧ β.imJ = 0 ∧ β.imK = 0
  · refine ⟨(s : ℚ)⁻¹ * β.re, ?_⟩
    rw [hγβ]
    ext <;> simp [hcen.1, hcen.2.1, hcen.2.2]

  exfalso

  have htβ : trd β = 2 * (s : ℚ) + (ℓ : ℚ) * T := by
    simp only [trd, re_smul, smul_eq_mul] at hT
    rw [hβ, hγ]
    simp only [trd, re_smul, re_add, re_one, smul_eq_mul]
    linear_combination (ℓ : ℚ) * hT
  have hmβ : nrd β = (s : ℚ) ^ 2 + (s : ℚ) * ℓ * T + (ℓ : ℚ) ^ 2 * M := by
    simp only [trd, nrd, re_smul, imI_smul, imJ_smul, imK_smul, smul_eq_mul] at hT hM
    rw [hβ, hγ]
    simp only [nrd, re_smul, imI_smul, imJ_smul, imK_smul, re_add, imI_add, imJ_add, imK_add,
      re_one, imI_one, imJ_one, imK_one, smul_eq_mul]
    linear_combination ((s : ℚ) * ℓ) * hT + (ℓ : ℚ) ^ 2 * hM

  have hβn : β ^ n = ((s : ℚ) ^ n * c) • (1 : ℍ[ℚ, a, b]) := by
    rw [hβ, smul_pow, hc, smul_smul]

  have hsq : β * β = trd β • β - nrd β • (1 : ℍ[ℚ, a, b]) := mul_self_eq_trd_smul_sub_nrd_smul β
  have hD : (trd β) ^ 2 < 4 * nrd β := trd_sq_lt_four_mul_nrd ha hb β hcen

  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hLuc := pow_succ_eq_lucasU (trd β) (nrd β) β hsq k
  have hUβ : lucasU (trd β) (nrd β) (k + 1) • β =
      ((s : ℚ) ^ (k + 1) * c + nrd β * lucasU (trd β) (nrd β) k) • (1 : ℍ[ℚ, a, b]) := by
    rw [add_smul, ← hβn, hLuc, sub_add_cancel]

  have hU0 : lucasU (trd β) (nrd β) (k + 1) = 0 := by
    by_contra hU
    have h1 := congrArg (fun v : ℍ[ℚ, a, b] => (lucasU (trd β) (nrd β) (k + 1))⁻¹ • v) hUβ
    simp only [smul_smul, inv_mul_cancel₀ hU, one_smul] at h1
    apply hcen
    rw [h1]
    simp

  have hcomplex : ∀ w : ℂ, w * w = ((trd β : ℚ) : ℂ) * w - ((nrd β : ℚ) : ℂ) →
      w ^ (k + 1) = ((-(nrd β * lucasU (trd β) (nrd β) k) : ℚ) : ℂ) := by
    intro w hw
    have hw' : w * w = trd β • w - nrd β • (1 : ℂ) := by
      rw [hw, Rat.smul_def, Rat.smul_one_eq_cast]
    rw [pow_succ_eq_lucasU (trd β) (nrd β) w hw' k, hU0, zero_smul, zero_sub,
      Rat.smul_one_eq_cast]
    push_cast
    ring
  obtain ⟨k', hk0, hk4, hk⟩ :=
    exists_int_sq_eq_mul_of_forall_root_pow_eq (trd β) (nrd β) _ hD (k + 1) (Nat.succ_pos k)
      hcomplex

  rw [htβ, hmβ] at hk
  have hZ : ((2 * (s : ℤ) + (ℓ : ℤ) * T) ^ 2 : ℤ) =
      k' * ((s : ℤ) ^ 2 + (s : ℤ) * ℓ * T + (ℓ : ℤ) ^ 2 * M) := by
    exact_mod_cast hk
  have hdvd : (ℓ : ℤ) ∣ (4 - k') * (s : ℤ) ^ 2 :=
    ⟨k' * ((s : ℤ) * T) + k' * ((ℓ : ℤ) * M) - 4 * ((s : ℤ) * T) - (ℓ : ℤ) * T ^ 2,
      by linear_combination hZ⟩
  have hℓZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  rcases hℓZ.dvd_or_dvd hdvd with h4 | hs2
  · have hpos : (0 : ℤ) < 4 - k' := by omega
    have hle := Int.le_of_dvd hpos h4
    omega
  · have h1 : (ℓ : ℤ) ∣ (s : ℤ) := hℓZ.dvd_of_dvd_pow hs2
    exact hs (by exact_mod_cast h1)

end MinkowskiSerreQuaternionRigidity

theorem solution
    {a b : ℚ} (ha : a < 0) (hb : b < 0) (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : IsOrder L)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (s : ℕ) (hs : ¬ ℓ ∣ s)
    (γ y : ℍ[ℚ, a, b]) (hy : (s : ℚ) • y ∈ L) (hγ : γ = 1 + (ℓ : ℚ) • y)
    (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : γ ^ n = c • (1 : ℍ[ℚ, a, b])) :
    ∃ c' : ℚ, γ = c' • (1 : ℍ[ℚ, a, b]) :=
  MinkowskiSerreQuaternionRigidity.rigidity ha hb L hL ℓ hℓ hℓ5 s hs γ y hy hγ n hn c hc

end S_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
end P2MW
export P2MW.S_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul (solution)
