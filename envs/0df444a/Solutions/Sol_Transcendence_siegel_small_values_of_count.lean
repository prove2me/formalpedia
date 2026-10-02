-- Prove2me | solution 1 for Transcendence.siegel_small_values_of_count
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:49:40.308983+00:00
-- url     : https://prove2.me/submissions/10ed13f8-1dc8-48ed-b24a-87b31d192ecb

import Mathlib
import Theorems.Thm_Transcendence_thue_siegel_real
import Theorems.Thm_Transcendence_taylor_tail_le
import Theorems.Thm_Transcendence_taylor_coeff_forms

/-!
# An auxiliary function with small values, for given parameters (DALAG Prop. 4.10)

The `Tⁿ` Cauchy-bounded Taylor coefficient forms of `Transcendence.taylor_coeff_forms` (radius `r`)
are made small by the complex Thue–Siegel lemma (Lemma 4.12, `siegel_complex`: real and imaginary
parts go separately into `Transcendence.thue_siegel_real`, a factor `2` in place of `√2`). So the
Taylor polynomial of order `< T` of `F = Σ_λ p_λ φ_λ` is at most `Tⁿ · 2CX/ℓ` on the polydisc of
radius `r`; as `|F| ≤ XC` on the polydisc of radius `R`, the tail is at most
`XC (r/R)^T / (1 - r/R)` by `Transcendence.taylor_tail_le`.
-/

namespace SiegelSmallValuesOfCount

/-- **Lemma 4.12** (complex version, with real and imaginary parts treated separately):
complex forms with `∑ ‖u j l‖ ≤ C`, and `ℓ^{2μ} < (X+1)^ν`. -/
lemma siegel_complex {J Λ : Type*} [Fintype J] [Fintype Λ] (u : J → Λ → ℂ) {C : ℝ}
    (hC : 0 < C) (hu : ∀ j, ∑ l, ‖u j l‖ ≤ C) {X ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcard : ℓ ^ (2 * Fintype.card J) < (X + 1) ^ Fintype.card Λ) :
    ∃ ξ : Λ → ℤ, ξ ≠ 0 ∧ (∀ l, |ξ l| ≤ X) ∧
      ∀ j, ‖∑ l, u j l * (ξ l : ℂ)‖ ≤ 2 * (C * X / ℓ) := by
  let v : J ⊕ J → Λ → ℝ := fun j l => Sum.elim (fun j => (u j l).re) (fun j => (u j l).im) j
  have hv : ∀ j, ∑ l, |v j l| ≤ C := by
    rintro (j | j)
    · exact le_trans (Finset.sum_le_sum fun l _ => Complex.abs_re_le_norm (u j l)) (hu j)
    · exact le_trans (Finset.sum_le_sum fun l _ => Complex.abs_im_le_norm (u j l)) (hu j)
  have hc : ℓ ^ Fintype.card (J ⊕ J) < (X + 1) ^ Fintype.card Λ := by
    rwa [Fintype.card_sum, ← two_mul]
  obtain ⟨ξ, hξ0, hξX, hξ⟩ := Transcendence.thue_siegel_real v hC hv hℓ hc
  refine ⟨ξ, hξ0, hξX, fun j => ?_⟩
  have hre : (∑ l, u j l * (ξ l : ℂ)).re = ∑ l, v (Sum.inl j) l * ξ l := by
    simp [v, Complex.re_sum]
  have him : (∑ l, u j l * (ξ l : ℂ)).im = ∑ l, v (Sum.inr j) l * ξ l := by
    simp [v, Complex.im_sum]
  calc ‖∑ l, u j l * (ξ l : ℂ)‖
      ≤ |(∑ l, u j l * (ξ l : ℂ)).re| + |(∑ l, u j l * (ξ l : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ C * X / ℓ + C * X / ℓ := by rw [hre, him]; exact add_le_add (hξ _) (hξ _)
    _ = 2 * (C * X / ℓ) := by ring

end SiegelSmallValuesOfCount

theorem solution {ι Λ : Type*} [Fintype ι] [Fintype Λ]
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ) {r R C : ℝ}
    (hr : 0 < r) (hrR : r < R) (B : Λ → ℝ)
    (hB : ∀ l, ∀ z ∈ Metric.closedBall (0 : ι → ℂ) R, ‖φ l z‖ ≤ B l)
    (hC : 0 < C) (hBC : ∑ l, B l ≤ C) {T X ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcount : ℓ ^ (2 * T ^ Fintype.card ι) < (X + 1) ^ Fintype.card Λ) :
    ∃ p : Λ → ℤ, p ≠ 0 ∧ (∀ l, |p l| ≤ X) ∧
      ∀ z ∈ Metric.closedBall (0 : ι → ℂ) r, ‖∑ l, (p l : ℂ) * φ l z‖ ≤
        (T : ℝ) ^ Fintype.card ι * (2 * (C * X / ℓ)) + X * C * (r / R) ^ T / (1 - r / R) := by
  classical
  have hR : 0 < R := hr.trans hrR
  -- the linear forms: the Cauchy-bounded Taylor coefficients of order `< T`, radius `r`
  obtain ⟨u, hu, hTaylor⟩ := Transcendence.taylor_coeff_forms φ hφ hr B
    (fun l z hz => hB l z (Metric.closedBall_subset_closedBall hrR.le hz)) T
  have hcount' : ℓ ^ (2 * Fintype.card (ι → Fin T)) < (X + 1) ^ Fintype.card Λ := by
    rwa [Fintype.card_fun, Fintype.card_fin]
  -- Lemma 4.12: the forms are small at some integer point `p`
  obtain ⟨p, hp0, hpX, hpu⟩ := SiegelSmallValuesOfCount.siegel_complex u hC
    (fun τ => (Finset.sum_le_sum fun l _ => hu τ l).trans hBC) hℓ hcount'
  refine ⟨p, hp0, hpX, fun z hz => ?_⟩
  have hpX' : ∀ l, |(p l : ℝ)| ≤ X := fun l => by
    rw [← Int.cast_abs]; exact_mod_cast hpX l
  have hid := hTaylor (fun l => (p l : ℂ)) z
  set F : (ι → ℂ) → ℂ := fun x => ∑ l, (p l : ℂ) * φ l x with hFdef
  have hF : AnalyticOnNhd ℂ F Set.univ :=
    Finset.analyticOnNhd_fun_sum _ (fun l _ => analyticOnNhd_const.mul (hφ l))
  have hFM : ∀ x ∈ Metric.closedBall (0 : ι → ℂ) R, ‖F x‖ ≤ X * C := by
    intro x hx
    calc ‖F x‖ ≤ ∑ l, ‖(p l : ℂ) * φ l x‖ := norm_sum_le _ _
      _ ≤ ∑ l, (X : ℝ) * B l := by
          apply Finset.sum_le_sum; intro l _
          rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul (hpX' l) (hB l x hx) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = X * ∑ l, B l := by rw [Finset.mul_sum]
      _ ≤ X * C := mul_le_mul_of_nonneg_left hBC (Nat.cast_nonneg _)
  have hz' : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
  set P := ∑ k ∈ Finset.range T, (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k F 0 (fun _ => z)
    with hP
  -- the Taylor polynomial of order `< T` is small on the polydisc of radius `r`
  have hhead : ‖P‖ ≤ (T : ℝ) ^ Fintype.card ι * (2 * (C * X / ℓ)) := by
    have hy1 : ∀ ν, ‖z ν / (r : ℂ)‖ ≤ 1 := fun ν => by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_le_one hr]
      exact (norm_le_pi_norm z ν).trans hz'
    rw [hid]
    calc ‖∑ τ : ι → Fin T, (∏ ν, (z ν / r) ^ (τ ν : ℕ)) * ∑ l, u τ l * (p l : ℂ)‖
        ≤ ∑ τ : ι → Fin T, 2 * (C * X / ℓ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
          rw [norm_mul]
          have h1 : ‖∏ ν, (z ν / r) ^ (τ ν : ℕ)‖ ≤ 1 := by
            rw [norm_prod]
            calc ∏ ν, ‖(z ν / r) ^ (τ ν : ℕ)‖ ≤ ∏ _ν : ι, (1 : ℝ) := by
                  gcongr with ν
                  rw [norm_pow]
                  exact pow_le_one₀ (norm_nonneg _) (hy1 ν)
              _ = 1 := Finset.prod_const_one
          calc _ ≤ 1 * (2 * (C * X / ℓ)) := mul_le_mul h1 (hpu τ) (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = (T : ℝ) ^ Fintype.card ι * (2 * (C * X / ℓ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  -- the tail of the Taylor series (Lemma 4.13)
  have htail : ‖F z - P‖ ≤ X * C * (r / R) ^ T / (1 - r / R) :=
    Transcendence.taylor_tail_le hF hr hrR hFM hz' T
  calc ‖F z‖ ≤ ‖P‖ + ‖F z - P‖ := by
        have := norm_add_le P (F z - P); rwa [add_sub_cancel] at this
    _ ≤ _ := add_le_add hhead htail
