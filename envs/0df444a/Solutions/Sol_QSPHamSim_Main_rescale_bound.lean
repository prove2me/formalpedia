-- Prove2me | solution 1 for QSPHamSim.Main.rescale_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:50:52.364339+00:00
-- url     : https://prove2.me/submissions/fa65f9b4-80bb-4936-976b-e02d67ed1ede

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

theorem solution (A C h : ℝ → ℝ) (ε : ℝ)
    (happrox : ∀ θ : ℝ,
      ‖((A θ : ℂ) + (C θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ ε) :
    let A₁ := fun θ : ℝ => A θ / (1 + ε)
    let C₁ := fun θ : ℝ => C θ / (1 + ε)
    (∀ θ : ℝ,
      ‖((A₁ θ : ℂ) + (C₁ θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 2 * ε ∧
      A₁ θ ^ 2 + C₁ θ ^ 2 ≤ 1) ∧
    (ε ≤ 1 → ∀ θ : ℝ,
      ((1 - ε) / (1 + ε)) ^ 2 ≤ A₁ θ ^ 2 + C₁ θ ^ 2) ∧
    (h 0 = 0 → C 0 = 0 →
      (1 - ε) / (1 + ε) ≤ A₁ 0 ∧ A₁ 0 ≤ 1 ∧
      ∃ δ : ℝ, Real.cos δ = A₁ 0 ∧
        (1 - ε) / (1 + ε) ≤ Real.cos δ) := by
  dsimp only
  have he : 0 ≤ ε := (norm_nonneg _).trans (happrox 0)
  have hd : 0 < 1 + ε := by linarith
  let z : ℝ → ℂ := fun θ => (A θ : ℂ) + (C θ : ℂ) * Complex.I
  let u : ℝ → ℂ := fun θ => Complex.exp ((h θ : ℂ) * Complex.I)
  let z₁ : ℝ → ℂ := fun θ => ((A θ / (1 + ε) : ℝ) : ℂ) +
    ((C θ / (1 + ε) : ℝ) : ℂ) * Complex.I
  have hu (θ : ℝ) : ‖u θ‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hnorm (θ : ℝ) : ‖z θ‖ ≤ 1 + ε := by
    have ht := norm_sub_norm_le (z θ) (u θ)
    rw [hu] at ht
    linarith [happrox θ]
  have hz₁ (θ : ℝ) : z₁ θ = (1 / (1 + ε) : ℝ) • z θ := by
    simp only [z₁, z, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    ring
  have hn₁ (θ : ℝ) : ‖z₁ θ‖ = ‖z θ‖ / (1 + ε) := by
    rw [hz₁, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
    ring
  have hsq (θ : ℝ) : ‖z₁ θ‖ ^ 2 = (A θ / (1 + ε)) ^ 2 + (C θ / (1 + ε)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [z₁, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      one_mul, mul_one, sub_zero, add_zero, zero_add, pow_two]
  have hupper (θ : ℝ) : ‖z₁ θ‖ ≤ 1 := by
    rw [hn₁]
    exact (div_le_one hd).2 (hnorm θ)
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    have heq : z₁ θ - z θ = (-ε / (1 + ε) : ℝ) • z θ := by
      rw [hz₁]
      calc
        _ = (1 / (1 + ε) : ℝ) • z θ - (1 : ℝ) • z θ := by rw [one_smul]
        _ = (1 / (1 + ε) - 1 : ℝ) • z θ := (sub_smul _ _ _).symm
        _ = _ := by congr 1; field_simp; ring
    have hdiff : ‖z₁ θ - z θ‖ ≤ ε := by
      rw [heq, norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg he, abs_of_pos hd]
      calc
        ε / (1 + ε) * ‖z θ‖ ≤ ε / (1 + ε) * (1 + ε) :=
          mul_le_mul_of_nonneg_left (hnorm θ) (div_nonneg he hd.le)
        _ = ε := div_mul_cancel₀ _ hd.ne'
    constructor
    · change ‖z₁ θ - u θ‖ ≤ 2 * ε
      have ht : ‖z₁ θ - u θ‖ ≤ ‖z₁ θ - z θ‖ + ‖z θ - u θ‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (z₁ θ - z θ) (z θ - u θ)
      linarith [happrox θ]
    · rw [← hsq]
      exact (sq_le_one_iff_abs_le_one _).2 (by simpa only [abs_norm] using hupper θ)
  · intro he1 θ
    have ht := norm_sub_norm_le (u θ) (z θ)
    rw [hu, norm_sub_rev] at ht
    have hlo : (1 - ε) / (1 + ε) ≤ ‖z₁ θ‖ := by
      rw [hn₁]
      exact div_le_div_of_nonneg_right (by linarith [happrox θ]) hd.le
    rw [← hsq]
    exact (sq_le_sq₀ (div_nonneg (by linarith) hd.le) (norm_nonneg _)).2 hlo
  · intro hh hC
    have hzero : |A 0 - 1| ≤ ε := by
      have hz := happrox 0
      simp only [hC, hh, Complex.ofReal_zero, zero_mul, add_zero, Complex.exp_zero] at hz
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hz
      exact hz
    have ha0 : (1 - ε) / (1 + ε) ≤ A 0 / (1 + ε) :=
      div_le_div_of_nonneg_right (by linarith [(abs_le.1 hzero).1]) hd.le
    have ha1 : A 0 / (1 + ε) ≤ 1 :=
      (div_le_one hd).2 (by linarith [(abs_le.1 hzero).2])
    have ham1 : -1 ≤ A 0 / (1 + ε) := by
      apply le_trans _ ha0
      apply (le_div_iff₀ hd).2
      linarith
    refine ⟨ha0, ha1, Real.arccos (A 0 / (1 + ε)), ?_, ?_⟩
    · exact Real.cos_arccos ham1 ha1
    · simpa only [Real.cos_arccos ham1 ha1] using ha0

#print axioms solution
