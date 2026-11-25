-- Prove2me | solution 1 for SmallRatio.legendre_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:03.752125+00:00
-- url     : https://prove2.me/submissions/9d6296e0-875c-4318-a448-61adfcda8477

module
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_Legendre
public import Theorems.Thm_SmallRatio_y_congr
public import Theorems.Thm_SmallRatio_y_det
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_steps
public import Theorems.Thm_SmallRatio_rem_zero
attribute [local simp] SmallRatio.den_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.rem_zero



set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
set_option maxHeartbeats 1000000
namespace SmallRatio
theorem _root_.solution (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : Nat.Coprime u v)
    (hsmall : 2 * u * v < k) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hcong : (k : ℤ) ∣ (h : ℤ) * v - ε * u) :
    ∃ j ∈ Icc 1 (steps k h), rem k h j = u ∧ den k h j = v ∧ ε = (-1) ^ (j + 1) := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hex : ∃ j, rem k h j ≤ u := ⟨steps k h, by rw [rem_steps hh hhk hc]; exact hu⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀le : j₀ ≤ steps k h := Nat.find_min' hex (by rw [rem_steps hh hhk hc]; exact hu)
  have hj₀spec : rem k h j₀ ≤ u := Nat.find_spec hex
  have hku : u < k := by
    have : u ≤ u * v := Nat.le_mul_of_pos_right u hv
    linarith
  have hj₀pos : 1 ≤ j₀ := by
    by_contra h0
    have : j₀ = 0 := by omega
    rw [this, rem_zero] at hj₀spec
    omega
  obtain ⟨i, hi⟩ : ∃ i, j₀ = i + 1 := ⟨j₀ - 1, by omega⟩
  have hri : u < rem k h i := by
    have := Nat.find_min hex (show i < j₀ by omega)
    omega
  have hri' : rem k h (i + 1) ≤ u := hi ▸ hj₀spec
  have hin : i + 1 ≤ steps k h := hi ▸ hj₀le
  -- notation
  set r := (rem k h i : ℤ) with hr
  set r' := (rem k h (i + 1) : ℤ) with hr'
  set y := (-1 : ℤ) ^ (i + 1) * den k h i with hy
  set y' := (-1 : ℤ) ^ (i + 2) * den k h (i + 1) with hy'
  set d' := (den k h (i + 1) : ℤ) with hd'
  have hdet : r * y' - r' * y = (-1) ^ i * k := y_det hh hhk hc (by omega)
  have hcy := y_congr (k := k) (h := h) i
  have hcy' := y_congr (k := k) (h := h) (i + 1)
  simp only [show i + 1 + 1 = i + 2 by ring] at hcy'
  -- Cramer's rule: the numerators are divisible by `k`
  obtain ⟨a₀, ha₀⟩ : (k : ℤ) ∣ (u : ℤ) * y' - ε * v * r' := by
    have e : (u : ℤ) * y' - ε * v * r' =
        y' * (-ε * ((h : ℤ) * v - ε * u)) + ε * v * ((h : ℤ) * y' - r') := by
      linear_combination (-(u : ℤ) * y') * hε2
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hcong _) _)
      (dvd_mul_of_dvd_right hcy' _)
  obtain ⟨b₀, hb₀⟩ : (k : ℤ) ∣ r * (ε * v) - y * u := by
    have e : r * (ε * v) - y * u =
        -ε * v * ((h : ℤ) * y - r) + y * (ε * ((h : ℤ) * v - ε * u)) := by
      linear_combination (y * (u : ℤ)) * hε2
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hcy _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hcong _) _)
  have hs2 : ((-1 : ℤ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set α := (-1 : ℤ) ^ i * a₀ with hα
  set β := (-1 : ℤ) ^ i * b₀ with hβ
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hXu : α * r + β * r' = u := by
    apply mul_left_cancel₀ hk0
    linear_combination ((k : ℤ) * r) * hα + ((k : ℤ) * r') * hβ - (-1 : ℤ) ^ i * r * ha₀
      - (-1 : ℤ) ^ i * r' * hb₀ + (-1 : ℤ) ^ i * (u : ℤ) * hdet + (u : ℤ) * k * hs2
  have hXv : α * y + β * y' = ε * v := by
    apply mul_left_cancel₀ hk0
    linear_combination ((k : ℤ) * y) * hα + ((k : ℤ) * y') * hβ - (-1 : ℤ) ^ i * y * ha₀
      - (-1 : ℤ) ^ i * y' * hb₀ + (-1 : ℤ) ^ i * (ε * v) * hdet + (ε * v) * k * hs2
  have hr'pos : (1 : ℤ) ≤ r' := by
    have := pos_rem_of_le_steps hh hhk hc hin; simp only [hr']; exact_mod_cast this
  have hd'0 : (0 : ℤ) ≤ d' := by positivity
  have hyy : y * y' ≤ 0 := by
    have : y * y' = -(((-1 : ℤ) ^ i) ^ 2 * (den k h i * d')) := by
      simp only [hy, hy', hd']; ring
    rw [this, hs2, one_mul, neg_nonpos]; positivity
  have hy'2 : y' ^ 2 = d' ^ 2 := by
    have : y' ^ 2 = ((-1 : ℤ) ^ i) ^ 2 * d' ^ 2 := by simp only [hy', hd']; ring
    rw [this, hs2, one_mul]
  have hvq : (1 : ℤ) ≤ v := by exact_mod_cast hv
  have huq : (1 : ℤ) ≤ u := by exact_mod_cast hu
  have hriq : (u : ℤ) < r := by simp only [hr]; exact_mod_cast hri
  have hri'q : r' ≤ (u : ℤ) := by simp only [hr']; exact_mod_cast hri'
  have hsmallq : 2 * (u : ℤ) * v < k := by exact_mod_cast hsmall
  have hy'abs : |y'| = d' := by
    rw [← abs_of_nonneg hd'0, ← sq_eq_sq_iff_abs_eq_abs]; exact hy'2
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  clear_value r r' y y' d' α β
  rcases lt_trichotomy α 0 with hαn | hα0 | hαp
  · -- `α < 0`
    rcases le_or_gt β 0 with hβn | hβp
    · exfalso
      have h1 : α * r ≤ -1 * r := mul_le_mul_of_nonneg_right (by omega) (by linarith)
      have h2 : β * r' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβn (by linarith)
      linarith
    · exfalso
      -- opposite signs: `v ≥ Q_{i+1}` and `|α| k ≤ 2uv`
      have hprod : 0 ≤ α * β * (y * y') := mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg hαn.le hβp.le) hyy
      have hv2 : d' ^ 2 ≤ (v : ℤ) ^ 2 := by
        have h1 : (ε * v) ^ 2 = (v : ℤ) ^ 2 := by rw [mul_pow, hε2, one_mul]
        rw [← h1, ← hXv]
        have hexp : (α * y + β * y') ^ 2 = (α * y) ^ 2 + 2 * (α * β * (y * y')) + β ^ 2 * y' ^ 2 := by
          ring
        have hb2 : 1 ≤ β ^ 2 := by
          rcases le_or_gt 0 β with hb | hb
          · exact one_le_pow₀ (by omega)
          · have : 1 ≤ (-β) ^ 2 := one_le_pow₀ (by omega)
            simpa [neg_sq] using this
        have h3 : y' ^ 2 ≤ β ^ 2 * y' ^ 2 := by
          have := mul_le_mul_of_nonneg_right hb2 (sq_nonneg y'); simpa using this
        rw [hexp]
        linarith [sq_nonneg (α * y), hprod, h3, hy'2]
      have hdv : d' ≤ v := (pow_le_pow_iff_left₀ hd'0 (by positivity) two_ne_zero).1 hv2
      have hNa : |(u : ℤ) * y' - ε * v * r'| ≤ u * d' + v * r' := by
        calc |(u : ℤ) * y' - ε * v * r'| ≤ |(u : ℤ) * y'| + |ε * v * r'| := abs_sub _ _
          _ = u * d' + v * r' := by
            rw [abs_mul (u : ℤ) y', abs_mul (ε * (v : ℤ)) r', abs_mul ε (v : ℤ), hy'abs, hεabs,
              abs_of_nonneg (by positivity : (0 : ℤ) ≤ u),
              abs_of_nonneg (by positivity : (0 : ℤ) ≤ v), abs_of_nonneg (by linarith : (0 : ℤ) ≤ r')]
            ring
      rw [ha₀] at hNa
      have hαabs : |α| = |a₀| := by
        rw [hα, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have ha1 : 1 ≤ |a₀| := by rw [← hαabs]; rw [abs_of_neg hαn]; linarith
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)] at hNa
      have e1 : (k : ℤ) ≤ k * |a₀| := le_mul_of_one_le_right (by positivity) ha1
      have e2 : (u : ℤ) * d' ≤ u * v := mul_le_mul_of_nonneg_left hdv (by positivity)
      have e3 : (v : ℤ) * r' ≤ v * u := mul_le_mul_of_nonneg_left hri'q (by positivity)
      linarith
  · -- `α = 0`: `(u, εv) = β b_{i+1}`
    rw [hα0, zero_mul, zero_add] at hXu hXv
    have hβpos : 0 < β := by
      by_contra hb
      have : β * r' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by linarith)
      linarith
    have hβu : β ∣ (u : ℤ) := ⟨r', hXu.symm⟩
    have hβv : β ∣ (v : ℤ) := by
      refine ⟨ε * y', ?_⟩
      linear_combination (-(v : ℤ)) * hε2 - ε * hXv
    have hβ1 : β = 1 := by
      have hg : β ∣ (Int.gcd u v : ℤ) := Int.dvd_coe_gcd hβu hβv
      rw [Int.gcd_natCast_natCast, Nat.Coprime.gcd_eq_one huv] at hg
      have := Int.eq_one_of_dvd_one hβpos.le (by exact_mod_cast hg)
      exact this
    rw [hβ1, one_mul] at hXu hXv
    refine ⟨i + 1, mem_Icc.2 ⟨by omega, hin⟩, by rw [hr'] at hXu; exact_mod_cast hXu, ?_, ?_⟩
    · -- `εv = (-1)^{i+2} Q_{i+1}`, so `v = Q_{i+1}`
      have hv2 : (v : ℤ) ^ 2 = d' ^ 2 := by
        rw [← hy'2, hXv, mul_pow, hε2, one_mul]
      have : (v : ℤ) = d' := (pow_left_inj₀ (by positivity) hd'0 two_ne_zero).1 hv2
      rw [hd'] at this
      exact_mod_cast this.symm
    · -- the sign
      have hv2 : (v : ℤ) ^ 2 = d' ^ 2 := by
        rw [← hy'2, hXv, mul_pow, hε2, one_mul]
      have hvd : (v : ℤ) = d' := (pow_left_inj₀ (by positivity) hd'0 two_ne_zero).1 hv2
      have hs : ((-1 : ℤ) ^ (i + 2)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
      have : ε * v = (-1) ^ (i + 2) * v := by rw [← hXv, hy', hvd]
      have hv0 : (v : ℤ) ≠ 0 := by omega
      have := mul_right_cancel₀ hv0 this
      rw [this]
  · -- `α > 0`
    rcases le_or_gt 0 β with hβp | hβn
    · exfalso
      have h1 : 1 * r ≤ α * r := mul_le_mul_of_nonneg_right (by omega) (by linarith)
      have h2 : 0 ≤ β * r' := mul_nonneg hβp (by linarith)
      linarith
    · exfalso
      have hprod : 0 ≤ α * β * (y * y') := mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hαp.le hβn.le) hyy
      have hv2 : d' ^ 2 ≤ (v : ℤ) ^ 2 := by
        have h1 : (ε * v) ^ 2 = (v : ℤ) ^ 2 := by rw [mul_pow, hε2, one_mul]
        rw [← h1, ← hXv]
        have hexp : (α * y + β * y') ^ 2 = (α * y) ^ 2 + 2 * (α * β * (y * y')) + β ^ 2 * y' ^ 2 := by
          ring
        have hb2 : 1 ≤ β ^ 2 := by
          rcases le_or_gt 0 β with hb | hb
          · exact one_le_pow₀ (by omega)
          · have : 1 ≤ (-β) ^ 2 := one_le_pow₀ (by omega)
            simpa [neg_sq] using this
        have h3 : y' ^ 2 ≤ β ^ 2 * y' ^ 2 := by
          have := mul_le_mul_of_nonneg_right hb2 (sq_nonneg y'); simpa using this
        rw [hexp]
        linarith [sq_nonneg (α * y), hprod, h3, hy'2]
      have hdv : d' ≤ v := (pow_le_pow_iff_left₀ hd'0 (by positivity) two_ne_zero).1 hv2
      have hNa : |(u : ℤ) * y' - ε * v * r'| ≤ u * d' + v * r' := by
        calc |(u : ℤ) * y' - ε * v * r'| ≤ |(u : ℤ) * y'| + |ε * v * r'| := abs_sub _ _
          _ = u * d' + v * r' := by
            rw [abs_mul (u : ℤ) y', abs_mul (ε * (v : ℤ)) r', abs_mul ε (v : ℤ), hy'abs, hεabs,
              abs_of_nonneg (by positivity : (0 : ℤ) ≤ u),
              abs_of_nonneg (by positivity : (0 : ℤ) ≤ v), abs_of_nonneg (by linarith : (0 : ℤ) ≤ r')]
            ring
      rw [ha₀] at hNa
      have hαabs : |α| = |a₀| := by
        rw [hα, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have ha1 : 1 ≤ |a₀| := by rw [← hαabs]; rw [abs_of_pos hαp]; linarith
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)] at hNa
      have e1 : (k : ℤ) ≤ k * |a₀| := le_mul_of_one_le_right (by positivity) ha1
      have e2 : (u : ℤ) * d' ≤ u * v := mul_le_mul_of_nonneg_left hdv (by positivity)
      have e3 : (v : ℤ) * r' ≤ v * u := mul_le_mul_of_nonneg_left hri'q (by positivity)
      linarith
end SmallRatio
