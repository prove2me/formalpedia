-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_quasiPeriodic_eq_zero_46166fd09bf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:35.703801+00:00
-- url     : https://prove2.me/submissions/20012756-3eb6-4242-9444-5702c538b4a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_const_2c6dde38f7a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_shift_057157dc3f1b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (n : ℕ) (hn : 0 < n) (h : ℂ → ℂ) (hd : Differentiable ℂ h) (C : ℂ)
    (hC : C ≠ 0) (h1 : ∀ w, h (w + 1) = h w)
    (h2 : ∀ w, h (w + I) = C * cexp (-2 * π * I * n * w) * h w)
    (h0 : ∀ k : ℕ, k < n → ∫ x in (0 : ℝ)..1, h x * cexp (-2 * π * I * k * x) = 0) : h = 0 := by

  have hrec : ∀ k : ℤ, lineCoeff h k 0 = C * cexp (2 * π * k) * lineCoeff h (k + n) 0 := by
    intro k
    rw [lineCoeff_const h hd h1 k 0 (0 + 1), lineCoeff_shift h n C h2]
  have hne : ∀ k : ℤ, C * cexp (2 * π * k) ≠ 0 := fun k => mul_ne_zero hC (Complex.exp_ne_zero _)
  have base : ∀ r : ℕ, r < n → lineCoeff h r 0 = 0 := by
    intro r hr
    simpa [lineCoeff] using h0 r hr
  have hq : ∀ q : ℤ, ∀ r : ℕ, r < n → lineCoeff h (q * n + r) 0 = 0 := by
    intro q r hr
    induction q using Int.induction_on with
    | zero => simpa using base r hr
    | succ q ih =>
      have := hrec (q * n + r)
      rw [ih, show (q : ℤ) * n + r + n = (q + 1) * n + r by ring] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (hne _)
    | pred q ih =>
      have := hrec ((-(q : ℤ) - 1) * n + r)
      rw [show (-(q : ℤ) - 1) * n + r + n = -(q : ℤ) * n + r by ring, ih, mul_zero] at this
      exact this
  have hall : ∀ (k : ℤ) (y : ℝ), lineCoeff h k y = 0 := by
    intro k y
    rw [lineCoeff_const h hd h1 k y 0]
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hlt := Int.emod_lt_of_pos k hn'
    have hnn := Int.emod_nonneg k hn'.ne'
    have := hq (k / n) (k % n).toNat (by omega)
    rwa [Int.toNat_of_nonneg (Int.emod_nonneg k hn'.ne'), Int.ediv_mul_add_emod] at this

  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hint : ∀ m : ℤ, ∀ w, h (w + m) = h w := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih => intro w; push_cast at ih ⊢; rw [← add_assoc, h1, ih]
    | pred m ih =>
      intro w; push_cast at ih ⊢
      rw [← h1 (w + (-(m : ℂ) - 1)), show w + (-(m : ℂ) - 1) + 1 = w + -(m : ℂ) by ring, ih]
  have hline : ∀ (y x : ℝ), x ∈ Set.Ico (0 : ℝ) (0 + 1) → h (x + y * I) = 0 := by
    intro y x hx
    set g : ℝ → ℂ := fun x => h (x + y * I) with hg
    have hgc : Continuous g := hd.continuous.comp (by fun_prop)
    have hg01 : g 0 = g (0 + 1) := by
      simp only [hg]; push_cast
      rw [show (0 : ℂ) + 1 + y * I = (0 + y * I) + 1 by ring, h1]
    let f : C(AddCircle (1 : ℝ), ℂ) :=
      ⟨AddCircle.liftIco 1 0 g, AddCircle.liftIco_continuous hg01 hgc.continuousOn⟩
    have hcoef : ∀ k : ℤ, fourierCoeff f k = 0 := by
      intro k
      change fourierCoeff (AddCircle.liftIco 1 0 g) k = 0
      rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
      have e : ∀ x : ℝ, fourier (-k) (x : AddCircle ((0 : ℝ) + 1 - 0)) • g x =
          cexp (-2 * π * k * y) * (h (x + y * I) * cexp (-2 * π * I * k * (x + y * I))) := by
        intro x
        rw [fourier_coe_apply, smul_eq_mul]
        have : cexp (2 * π * I * ((-k : ℤ) : ℂ) * x / ((0 + 1 - 0 : ℝ) : ℂ)) =
            cexp (-2 * π * k * y) * cexp (-2 * π * I * k * (x + y * I)) := by
          rw [← Complex.exp_add]; congr 1; push_cast
          linear_combination (2 * π * k * y) * I_sq
        rw [this]; simp only [hg]; ring
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul]
      have := hall k y
      simp only [lineCoeff] at this
      simp only [zero_add, this, mul_zero, smul_zero]
    have hs := has_pointwise_sum_fourier_series_of_summable (f := f)
      (by rw [show fourierCoeff f = fun _ => 0 from funext hcoef]; exact summable_zero) (x : AddCircle (1 : ℝ))
    simp only [hcoef, zero_smul] at hs
    have h0f : f (x : AddCircle (1 : ℝ)) = g x := by
      change AddCircle.liftIco 1 0 g (x : AddCircle (1 : ℝ)) = g x
      exact AddCircle.liftIco_coe_apply hx
    change g x = 0
    rw [← h0f]
    exact (hasSum_zero.unique hs).symm
  funext w
  have hx : Int.fract w.re ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    rw [zero_add]; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have := hline w.im (Int.fract w.re) hx
  rw [← hint ⌊w.re⌋] at this
  have hw : ((Int.fract w.re : ℝ) : ℂ) + w.im * I + (⌊w.re⌋ : ℂ) = w := by
    apply Complex.ext
    · simp [Int.fract_add_floor]
    · simp
  rw [hw] at this
  simpa using this
end GroundTheory.Heights₂.Heights.KeyFormula
