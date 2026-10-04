-- Prove2me | solution 1 for TaoFivePrimes.theorem51_vaughan_split_uncentered
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T02:41:03.787786+00:00
-- url     : https://prove2.me/submissions/a5ce41ac-3e4d-4f00-8468-16cdbe10cf02

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Definitions.Def_TaoFivePrimes_VaughanTruncation
import Theorems.Thm_TaoFivePrimes_vaughan_decomposition
import Theorems.Thm_TaoFivePrimes_vaughan_typeI_coeff_le_log

open Finset

section PartV51
open Finset
namespace TaoV51

open TaoFivePrimes

theorem eta0_eq_zero_of_le {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with h0
  · have h1 : Real.log (2 * t) ≤ Real.log 2 + Real.log (1/4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      apply Real.log_le_log (by linarith)
      linarith
    have h2 : Real.log (1/4) = -(2 * Real.log 2) := by
      rw [show (1:ℝ)/4 = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      ring
    have h3 : Real.log (2 * t) ≤ -Real.log 2 := by rw [h2] at h1; linarith
    have h4 : Real.log 2 ≤ |Real.log (2 * t)| := by
      have : Real.log 2 ≤ -Real.log (2*t) := by linarith
      calc Real.log 2 ≤ -Real.log (2*t) := this
        _ ≤ |Real.log (2*t)| := neg_le_abs _
    rw [max_eq_left (by linarith)]
    ring
  · rfl

theorem eta0_eq_zero_of_ge {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  split_ifs with h0
  · have h1 : Real.log 2 ≤ Real.log (2 * t) := by
      apply Real.log_le_log (by norm_num); linarith
    have h4 : Real.log 2 ≤ |Real.log (2 * t)| := le_trans h1 (le_abs_self _)
    rw [max_eq_left (by linarith)]
    ring
  · rfl

theorem eta0_eq_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : eta0 t = 0 := by
  unfold eta0
  rw [if_neg (by linarith)]

/-- The test function attached to `S_{eta0,2}(x, alpha)`. -/
noncomputable def FF (x alpha : ℝ) (n : ℕ) : ℂ :=
  if n.Coprime 2 then expCircle (alpha * n) * (eta0 ((n : ℝ) / x) : ℂ) else 0

theorem FF_even {x alpha : ℝ} {n : ℕ} (h : ¬ n.Coprime 2) : FF x alpha n = 0 := by
  unfold FF; rw [if_neg h]

theorem smoothedExpSum_eq_sum (x alpha : ℝ) (hx : 0 < x) (N : ℕ) (hN : x < N) :
    smoothedExpSum eta0 2 x alpha
      = ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * FF x alpha n := by
  unfold smoothedExpSum
  have hz : ∀ n : ℕ, n ∉ Finset.range N →
      (if Nat.Coprime n 2 then
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * expCircle (alpha * n) *
          ((eta0 ((n : ℝ) / x) : ℝ) : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ (n : ℝ) / x := by
      rw [le_div_iff₀ hx]; linarith
    rw [eta0_eq_zero_of_ge h2]
    simp
  rw [tsum_eq_sum hz]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold FF
  split_ifs with h
  · push_cast; ring
  · ring


theorem FF_zero_of_small {x alpha : ℝ} (hx : 0 < x) {n : ℕ} (h : 4 * (n : ℝ) < x) :
    FF x alpha n = 0 := by
  unfold FF
  have : (n : ℝ) / x ≤ 1/4 := by
    rw [div_le_iff₀ hx]; linarith
  rw [eta0_eq_zero_of_le this]
  split_ifs <;> simp

theorem FF_zero_of_big {x alpha : ℝ} (hx : 0 < x) {n : ℕ} (h : x < (n : ℝ)) :
    FF x alpha n = 0 := by
  unfold FF
  have : (1 : ℝ) ≤ (n : ℝ) / x := by
    rw [le_div_iff₀ hx]; linarith
  rw [eta0_eq_zero_of_ge this]
  split_ifs <;> simp

/-- The Type I inner sum, in the odd parametrization used by `theorem51TypeI`. -/
theorem typeI_inner (x alpha : ℝ) (hx : 0 < x) (N : ℕ) (hN : x < N)
    (d : ℕ) (hd : 0 < d) (hdodd : d.Coprime 2) (cd : ℂ) :
    (∑ m ∈ Finset.range N, ((ArithmeticFunction.log m : ℝ) : ℂ) * FF x alpha (d * m))
        + cd * (Real.log d : ℂ) *
          (∑ m ∈ Finset.range N, ((zetaR m : ℝ) : ℂ) * FF x alpha (d * m))
      = ∑' n : ℤ, (((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + cd * (Real.log d : ℂ)) *
          ((eta0 ((d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x) : ℝ) : ℂ)) *
          expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) := by
  classical
  set ψ : ℕ → ℂ := fun m =>
    ((Real.log m : ℝ) : ℂ) * FF x alpha (d * m)
      + cd * (Real.log d : ℂ) * (((zetaR m : ℝ) : ℂ) * FF x alpha (d * m)) with hψ
  set φ : ℤ → ℂ := fun n =>
    (((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + cd * (Real.log d : ℂ)) *
      ((eta0 ((d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x) : ℝ) : ℂ)) *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) with hφ
  have hlhs : (∑ m ∈ Finset.range N, ((ArithmeticFunction.log m : ℝ) : ℂ) * FF x alpha (d * m))
        + cd * (Real.log d : ℂ) *
          (∑ m ∈ Finset.range N, ((zetaR m : ℝ) : ℂ) * FF x alpha (d * m))
      = ∑ m ∈ Finset.range N, ψ m := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hψ]
    simp only [ArithmeticFunction.log_apply]
  rw [hlhs]
  -- the `ℤ`-sum is finitely supported
  have hsupp : ∀ n : ℤ, n ∉ (Finset.range N).image (fun k : ℕ => (k : ℤ)) → φ n = 0 := by
    intro n hn
    have hcase : n < 0 ∨ (N : ℤ) ≤ n := by
      by_contra hcon
      push_neg at hcon
      exact hn (Finset.mem_image.mpr ⟨n.toNat, Finset.mem_range.mpr (by omega),
        Int.toNat_of_nonneg hcon.1⟩)
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rcases hcase with h | h
    · have h1 : ((2 * n + 1 : ℤ) : ℝ) ≤ -1 := by
        have : (2 * n + 1 : ℤ) ≤ -1 := by omega
        exact_mod_cast this
      have : (d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hx.le
        nlinarith
      rw [hφ]
      simp only
      rw [eta0_eq_zero_of_nonpos this]
      simp
    · have h1 : (N : ℝ) ≤ ((2 * n + 1 : ℤ) : ℝ) := by
        have : (N : ℤ) ≤ 2 * n + 1 := by omega
        exact_mod_cast this
      have h2 : (1 : ℝ) ≤ (d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x := by
        rw [le_div_iff₀ hx]
        nlinarith
      rw [hφ]
      simp only
      rw [eta0_eq_zero_of_ge h2]
      simp
  rw [tsum_eq_sum hsupp, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  -- both sides are supported on the odd residues
  set O : Finset ℕ := (Finset.range N).filter (fun m => m % 2 = 1) with hO
  set Z : Finset ℕ := (Finset.range N).filter (fun k => 2 * k + 1 < N) with hZ
  have hLo : (∑ m ∈ Finset.range N, ψ m) = ∑ m ∈ O, ψ m := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro m hm hmO
    have hme : ¬ m % 2 = 1 := by
      intro hcon; exact hmO (Finset.mem_filter.mpr ⟨hm, hcon⟩)
    have : ¬ (d * m).Coprime 2 := by
      have h2 : 2 ∣ m := by omega
      intro hcop
      have : (2 : ℕ) ∣ d * m := Dvd.dvd.mul_left h2 d
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) this
      omega
    simp only [hψ, FF_even this, mul_zero, zero_add, add_zero]
  have hRo : (∑ k ∈ Finset.range N, φ (k : ℤ)) = ∑ k ∈ Z, φ (k : ℤ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hkZ
    have hbig : N ≤ 2 * k + 1 := by
      by_contra hcon
      exact hkZ (Finset.mem_filter.mpr ⟨hk, by omega⟩)
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h1 : (N : ℝ) ≤ ((2 * (k : ℤ) + 1 : ℤ) : ℝ) := by
      have : (N : ℤ) ≤ 2 * (k : ℤ) + 1 := by exact_mod_cast hbig
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ (d : ℝ) * ((2 * (k : ℤ) + 1 : ℤ) : ℝ) / x := by
      rw [le_div_iff₀ hx]
      nlinarith
    rw [hφ]
    simp only
    rw [eta0_eq_zero_of_ge h2]
    simp
  rw [hLo, hRo]
  refine (Finset.sum_nbij' (fun k => 2 * k + 1) (fun m => m / 2) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [hZ, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk.2, by omega⟩
  · intro m hm
    rw [hO, Finset.mem_filter, Finset.mem_range] at hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk; omega
  · intro m hm
    rw [hO, Finset.mem_filter] at hm
    omega
  · intro k hk
    rw [hZ, Finset.mem_filter, Finset.mem_range] at hk
    have hodd : (d * (2 * k + 1)).Coprime 2 := by
      refine Nat.Coprime.mul hdodd ?_
      exact Nat.coprime_two_right.mpr ⟨k, by ring⟩
    simp only [hψ, hφ, FF]
    rw [if_pos hodd]
    have hcast : (((d * (2 * k + 1) : ℕ)) : ℝ) = (d : ℝ) * ((2 * (k : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast; ring
    have hzeta : ((zetaR (2 * k + 1) : ℝ) : ℂ) = 1 := by
      simp [zetaR]
    have hlogm : ((Real.log ((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ)
        = ((Real.log ((2 * (k : ℤ) + 1 : ℤ) : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [hzeta, hcast, hlogm]
    push_cast
    ring

theorem truncGt_mul_zeta (V : ℝ) (w : ℕ) :
    (TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w
      = theorem51Centered V w + Real.log w / 2 := by
  rw [zetaR, ArithmeticFunction.coe_mul_zeta_apply, theorem51Centered]
  have : ∑ i ∈ w.divisors, TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt i
      = ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)), ArithmeticFunction.vonMangoldt b := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => by rw [TaoFivePrimes.truncGt_apply])
  rw [this]
  ring

theorem truncGt_mul_zeta_eq_zero {V : ℝ} {w : ℕ} (h : (w : ℝ) ≤ V) :
    (TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w = 0 := by
  rw [zetaR, ArithmeticFunction.coe_mul_zeta_apply]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [TaoFivePrimes.truncGt_apply, if_neg]
  intro hlt
  have hdvd : i ∣ w := (Nat.mem_divisors.mp hi).1
  have hw0 : w ≠ 0 := (Nat.mem_divisors.mp hi).2
  have : i ≤ w := Nat.le_of_dvd (Nat.pos_of_ne_zero hw0) hdvd
  have : (i : ℝ) ≤ (w : ℝ) := by exact_mod_cast this
  linarith

theorem coprime_two_mul {d w : ℕ} : (d * w).Coprime 2 ↔ d.Coprime 2 ∧ w.Coprime 2 := by
  constructor
  · intro h
    exact ⟨Nat.Coprime.coprime_dvd_left ⟨w, rfl⟩ h,
      Nat.Coprime.coprime_dvd_left ⟨d, by ring⟩ h⟩
  · rintro ⟨h1, h2⟩
    exact Nat.Coprime.mul h1 h2

/-- The Type II sum, in the doubly-indexed form used by `theorem51TypeII`. -/
theorem typeII_eq (x alpha U V : ℝ) (hx : 0 < x) (hU : 1 ≤ U) (N : ℕ) (hN : x < N) :
    (∑ d ∈ Finset.range N, ∑ w ∈ Finset.range N,
        ((TaoFivePrimes.truncGt U moebiusR d : ℝ) : ℂ) *
          (((TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w : ℝ) : ℂ) *
          FF x alpha (d * w))
      = ∑' d : ℕ, ∑' w : ℕ,
          (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (((theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
              expCircle (alpha * d * w) * ((eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
          else 0) := by
  classical
  set G : ℕ → ℕ → ℂ := fun d w =>
    (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (((theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
        expCircle (alpha * d * w) * ((eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
    else 0) with hG
  -- the two summands agree
  have hterm : ∀ d w : ℕ,
      ((TaoFivePrimes.truncGt U moebiusR d : ℝ) : ℂ) *
        (((TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w : ℝ) : ℂ) *
        FF x alpha (d * w) = G d w := by
    intro d w
    rw [hG]
    simp only
    by_cases hd : U < (d : ℝ)
    · by_cases hw : V < (w : ℝ)
      · by_cases hc : d.Coprime 2 ∧ w.Coprime 2
        · rw [if_pos ⟨hd, hw, hc.1, hc.2⟩, TaoFivePrimes.truncGt_apply, if_pos hd,
            truncGt_mul_zeta, FF, if_pos (coprime_two_mul.mpr hc)]
          have hcast : (((d * w : ℕ)) : ℝ) = (d : ℝ) * (w : ℝ) := by push_cast; ring
          rw [hcast]
          simp only [moebiusR, ArithmeticFunction.intCoe_apply]
          push_cast
          ring
        · rw [if_neg (by tauto), FF, if_neg (fun hcon => hc (coprime_two_mul.mp hcon))]
          ring
      · rw [if_neg (by tauto), truncGt_mul_zeta_eq_zero (not_lt.mp hw)]
        simp
    · rw [if_neg (by tauto), TaoFivePrimes.truncGt_apply, if_neg hd]
      simp
  simp only [hterm]
  -- the sums are finite
  have hGzero : ∀ d w : ℕ, N ≤ d ∨ N ≤ w → G d w = 0 := by
    intro d w h
    rw [hG]
    simp only
    by_cases hcond : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
    · rw [if_pos hcond]
      have hd1 : 1 ≤ d := by
        by_contra hcon
        have hd0 : d = 0 := by omega
        have h0 := hcond.1
        rw [hd0] at h0
        norm_num at h0
        linarith
      have hw1 : 1 ≤ w := by
        by_contra hcon
        have hw0 : w = 0 := by omega
        rw [hw0] at hcond
        have := hcond.2.2.2
        simp [Nat.Coprime] at this
      have hbig : (N : ℝ) ≤ (d : ℝ) * (w : ℝ) := by
        rcases h with h | h
        · have h1 : (N : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
          have h2 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1
          nlinarith [Nat.cast_nonneg (α := ℝ) d]
        · have h1 : (N : ℝ) ≤ (w : ℝ) := by exact_mod_cast h
          have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
          nlinarith [Nat.cast_nonneg (α := ℝ) w]
      have : (1 : ℝ) ≤ (d : ℝ) * (w : ℝ) / x := by
        rw [le_div_iff₀ hx]; linarith
      rw [eta0_eq_zero_of_ge this]
      simp
    · rw [if_neg hcond]
  have hinner : ∀ d : ℕ, (∑' w : ℕ, G d w) = ∑ w ∈ Finset.range N, G d w := by
    intro d
    refine tsum_eq_sum (fun w hw => hGzero d w (Or.inr ?_))
    rw [Finset.mem_range, not_lt] at hw; exact hw
  rw [tsum_congr hinner]
  refine (tsum_eq_sum (fun d hd => ?_)).symm
  rw [Finset.mem_range, not_lt] at hd
  exact Finset.sum_eq_zero (fun w _ => hGzero d w (Or.inl hd))

/-- The unit-modulus factor aligning two complex numbers. -/
noncomputable def align (S1 S0 : ℂ) : ℂ :=
  if S1 = 0 ∨ S0 = 0 then 1 else (S1 / (‖S1‖ : ℂ)) * ((‖S0‖ : ℂ) / S0)

theorem norm_align (S1 S0 : ℂ) : ‖align S1 S0‖ = 1 := by
  unfold align
  split_ifs with h
  · simp
  · push_neg at h
    rw [norm_mul, norm_div, norm_div]
    simp [Complex.norm_real, h.1, h.2]

theorem align_spec (S1 S0 : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖S1‖ + t * ‖S0‖ = ‖S1 + align S1 S0 * (t : ℂ) * S0‖ := by
  unfold align
  by_cases h1 : S1 = 0
  · rw [if_pos (Or.inl h1), h1]
    simp [abs_of_nonneg ht]
  · by_cases h0 : S0 = 0
    · rw [if_pos (Or.inr h0), h0]
      simp
    · rw [if_neg (by tauto)]
      have hn1 : (‖S1‖ : ℂ) ≠ 0 := by simpa using h1
      have hn0 : (‖S0‖ : ℂ) ≠ 0 := by simpa using h0
      have hkey : S1 / (‖S1‖ : ℂ) * ((‖S0‖ : ℂ) / S0) * (t : ℂ) * S0
          = S1 * ((t * ‖S0‖ / ‖S1‖ : ℝ) : ℂ) := by
        field_simp
        push_cast
        field_simp
      rw [hkey]
      have hfac : S1 + S1 * ((t * ‖S0‖ / ‖S1‖ : ℝ) : ℂ)
          = S1 * (((1 + t * ‖S0‖ / ‖S1‖ : ℝ)) : ℂ) := by push_cast; ring
      rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + t * ‖S0‖ / ‖S1‖)]
      have : ‖S1‖ ≠ 0 := by simpa using h1
      field_simp

theorem abs_moebiusR_le_one (d : ℕ) : |(moebiusR d : ℝ)| ≤ 1 := by
  simp only [moebiusR, ArithmeticFunction.intCoe_apply]
  by_cases h : Squarefree d
  · have h1 : (ArithmeticFunction.moebius d) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    have h2 : ((ArithmeticFunction.moebius d : ℝ)) ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℝ)), sq_abs ((ArithmeticFunction.moebius d : ℝ))]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp

theorem truncLe_mul_eq_zero {U V : ℝ} {d : ℕ} (h : U * V < (d : ℝ)) (hU : 0 < U) (hV : 0 < V) :
    (TaoFivePrimes.truncLe U moebiusR * TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt) d
      = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero (fun z hz => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hz
  rw [TaoFivePrimes.truncLe_apply, TaoFivePrimes.truncLe_apply]
  by_cases ha : (z.1 : ℝ) ≤ U
  · by_cases hb : (z.2 : ℝ) ≤ V
    · exfalso
      have hz1 : (0:ℝ) ≤ (z.1 : ℝ) := Nat.cast_nonneg _
      have hz2 : (0:ℝ) ≤ (z.2 : ℝ) := Nat.cast_nonneg _
      have : ((d : ℕ) : ℝ) = (z.1 : ℝ) * (z.2 : ℝ) := by
        rw [← hz.1]; push_cast; ring
      nlinarith
    · rw [if_neg hb]; ring
  · rw [if_neg ha]; ring

/-- **Tao, Lemma 4.11 applied to `S_{eta0,2}(x, alpha)`** (uncentred form): the Vaughan
Type I / Type II split. -/
theorem vaughan_split_uncentered (x alpha U V : ℝ)
    (hU : 40 ≤ U) (hV : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖smoothedExpSum eta0 2 x alpha‖ ≤
        theorem51TypeI x alpha U V c +
          ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (((theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
                expCircle (alpha * d * w) * ((eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
            else 0)‖ := by
  classical
  have hU0 : (0:ℝ) < U := by linarith
  have hV0 : (0:ℝ) < V := by linarith
  have hx : (0:ℝ) < x := by linarith
  set N : ℕ := ⌊x⌋₊ + 1 with hNdef
  have hN : x < N := by
    have h := Nat.lt_floor_add_one x
    rw [hNdef]; push_cast; exact h
  have hFN : ∀ n, N ≤ n → FF x alpha n = 0 := by
    intro n hn
    refine FF_zero_of_big hx ?_
    have : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hVsmall : 4 * V < x := by nlinarith
  have hFV : ∀ n : ℕ, (n : ℝ) ≤ V → FF x alpha n = 0 := by
    intro n hn
    exact FF_zero_of_small hx (by linarith)
  have hdecomp := TaoFivePrimes.vaughan_decomposition U V (FF x alpha) N hFN hFV
  have hsum := smoothedExpSum_eq_sum x alpha hx N hN
  set S1 : ℕ → ℂ := fun d =>
    ∑ m ∈ Finset.range N, ((ArithmeticFunction.log m : ℝ) : ℂ) * FF x alpha (d * m) with hS1
  set S0 : ℕ → ℂ := fun d =>
    ∑ m ∈ Finset.range N, ((zetaR m : ℝ) : ℂ) * FF x alpha (d * m) with hS0
  set e : ℕ → ℝ := fun d => TaoFivePrimes.truncLe U moebiusR d with he
  set f : ℕ → ℝ := fun d =>
    (TaoFivePrimes.truncLe U moebiusR *
      TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt) d with hf
  have hA : (∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ((TaoFivePrimes.truncLe U moebiusR d : ℝ) : ℂ) *
        ((ArithmeticFunction.log m : ℝ) : ℂ) * FF x alpha (d * m))
      = ∑ d ∈ Finset.range N, ((e d : ℝ) : ℂ) * S1 d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hS1, he]
    simp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hB : (∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
      (((TaoFivePrimes.truncLe U moebiusR *
          TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ) *
        ((zetaR m : ℝ) : ℂ) * FF x alpha (d * m))
      = ∑ d ∈ Finset.range N, ((f d : ℝ) : ℂ) * S0 d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hS0, hf]
    simp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  refine ⟨fun d => align (S1 d) (S0 d), fun d _ => le_of_eq (norm_align _ _), ?_⟩
  rw [hsum, hdecomp, hA, hB, typeII_eq x alpha U V hx (by linarith) N hN]
  refine le_trans (norm_add_le _ _) ?_
  have hmono : ∀ (a b c : ℝ), a ≤ b → a + c ≤ b + c := fun a b c h => by linarith
  refine hmono _ _ _ ?_
  -- the Type I estimate
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hsubs : theorem51Divisors U V ⊆ Finset.range N := by
    intro d hd
    rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc] at hd
    have h1 : (d : ℝ) ≤ U * V := by
      have := hd.1.2
      have h2 : (d : ℝ) ≤ (⌊U * V⌋₊ : ℝ) := by exact_mod_cast this
      exact le_trans h2 (Nat.floor_le (by positivity))
    have : (d : ℝ) < (N : ℝ) := by linarith
    exact Finset.mem_range.mpr (by exact_mod_cast this)
  have hzero : ∀ d ∈ Finset.range N, d ∉ theorem51Divisors U V →
      ‖((e d : ℝ) : ℂ) * S1 d - ((f d : ℝ) : ℂ) * S0 d‖ = 0 := by
    intro d _ hd
    have hd' : ¬ (1 ≤ d ∧ d ≤ ⌊U * V⌋₊ ∧ d.Coprime 2) := by
      rintro ⟨h1, h2, h3⟩
      refine hd ?_
      rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, h3⟩
    have hzero' : ((e d : ℝ) : ℂ) * S1 d - ((f d : ℝ) : ℂ) * S0 d = 0 := by
      by_cases hd0 : d = 0
      · subst hd0
        have h1 : e 0 = 0 := by rw [he]; simp [TaoFivePrimes.truncLe_apply, moebiusR]
        have h2 : f 0 = 0 := by rw [hf]; simp
        rw [h1, h2]; simp
      · by_cases hdc : d.Coprime 2
        · -- then `d` must exceed `U * V`
          have hbig : ⌊U * V⌋₊ < d := by
            by_contra hcon
            exact hd' ⟨by omega, by omega, hdc⟩
          have hbigR : U * V < (d : ℝ) := by
            rw [← Nat.floor_lt (by positivity)]
            exact hbig
          have h1 : e d = 0 := by
            rw [he]
            simp only [TaoFivePrimes.truncLe_apply]
            rw [if_neg]
            nlinarith
          have h2 : f d = 0 := by
            rw [hf]; exact truncLe_mul_eq_zero hbigR hU0 hV0
          rw [h1, h2]; simp
        · have hFz : ∀ m : ℕ, FF x alpha (d * m) = 0 := by
            intro m
            exact FF_even (fun hcon => hdc (coprime_two_mul.mp hcon).1)
          have h1 : S1 d = 0 := by
            rw [hS1]; simp only
            exact Finset.sum_eq_zero (fun m _ => by rw [hFz m]; ring)
          have h2 : S0 d = 0 := by
            rw [hS0]; simp only
            exact Finset.sum_eq_zero (fun m _ => by rw [hFz m]; ring)
          rw [h1, h2]; simp
    rw [hzero']; simp
  rw [← Finset.sum_subset hsubs hzero]
  rw [theorem51TypeI]
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hdm := hd
  rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc] at hdm
  have hd1 : 1 ≤ d := hdm.1.1
  have hdodd : d.Coprime 2 := hdm.2
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hbound : ‖((e d : ℝ) : ℂ) * S1 d - ((f d : ℝ) : ℂ) * S0 d‖
      ≤ ‖S1 d‖ + Real.log d * ‖S0 d‖ := by
    have hE : |e d| ≤ 1 := by
      rw [he]
      simp only [TaoFivePrimes.truncLe_apply]
      split_ifs
      · exact abs_moebiusR_le_one d
      · simp
    have hF : |f d| ≤ Real.log d := by
      rw [hf]; exact TaoFivePrimes.vaughan_typeI_coeff_le_log U V d
    calc ‖((e d : ℝ) : ℂ) * S1 d - ((f d : ℝ) : ℂ) * S0 d‖
        ≤ ‖((e d : ℝ) : ℂ) * S1 d‖ + ‖((f d : ℝ) : ℂ) * S0 d‖ := norm_sub_le _ _
      _ = |e d| * ‖S1 d‖ + |f d| * ‖S0 d‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖S1 d‖ + Real.log d * ‖S0 d‖ := by
          have := norm_nonneg (S1 d)
          have := norm_nonneg (S0 d)
          nlinarith
      _ = ‖S1 d‖ + Real.log d * ‖S0 d‖ := by ring
  rw [align_spec (S1 d) (S0 d) (Real.log d) hlogd] at hbound
  rw [typeI_inner x alpha hx N hN d (by omega) hdodd (align (S1 d) (S0 d))] at hbound
  exact hbound

end TaoV51
end PartV51

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c +
          ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (((TaoFivePrimes.theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
                TaoFivePrimes.expCircle (alpha * d * w) *
                ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
            else 0)‖ :=
  TaoV51.vaughan_split_uncentered x alpha U V hU hV hUx hVx hUVx hUV2
