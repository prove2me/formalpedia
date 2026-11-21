-- Prove2me | solution 1 for OAI.VerticalContourShift.exp_mellin_bound_of_polynomial_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:23:30.779192+00:00
-- url     : https://prove2.me/submissions/e5ba402f-e049-43bc-8143-5afd450311ed

import Theorems.Thm_OAI_VerticalContourShift_integral_eq_of_strip_decay
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology

theorem solution (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℂ → ℂ)
    (S : ℝ → ℂ) (k : ℂ)
    (hR : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ R z)
    (hpoly : ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖R z‖ ≤ C * (1 + |z.im|) ^ M)
    (hgamma : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖Complex.Gamma z‖ ≤ B / (1 + |z.im|) ^ m)
    (hinv : ∀ D : ℝ, 1 ≤ D → S D = k * ∫ t : ℝ,
      Complex.Gamma ((b : ℂ) + t * Complex.I) * (D : ℂ) ^ ((b : ℂ) + t * Complex.I) *
        R ((b : ℂ) + t * Complex.I)) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D → ‖S D‖ ≤ C * D ^ a := by
  obtain ⟨C, M, hC, _, hM⟩ := hpoly
  obtain ⟨n, hn⟩ := exists_nat_ge M
  obtain ⟨B, hB, hG⟩ := hgamma (n+2)
  refine ⟨1 + ‖k‖ * (B*C) * Real.pi, by positivity, ?_⟩
  intro D hD
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let f : ℂ → ℂ := fun z => Complex.Gamma z * (D : ℂ) ^ z * R z
  let line (σ t : ℝ) : ℂ := (σ : ℂ) + t * Complex.I
  have hRe (σ t : ℝ) : (line σ t).re = σ := by simp [line]
  have hIm (σ t : ℝ) : (line σ t).im = t := by simp [line]
  have hdiff (z : ℂ) (hz : a ≤ z.re) (hz' : z.re ≤ b) : DifferentiableAt ℂ f z := by
    have hgam := Complex.differentiableAt_Gamma z (fun m hm => by
      have hre := congrArg Complex.re hm
      have hpos := ha.trans_le hz
      simp at hre
      exact (not_lt_of_ge (Nat.cast_nonneg m : (0:ℝ) ≤ m)) (by linarith))
    have hdcp : DifferentiableAt ℂ (fun w : ℂ => (D : ℂ) ^ w) z :=
      differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hDp.ne'))
    exact (hgam.mul hdcp).mul (hR z hz hz')
  have hpoint (σ : ℝ) (hσ : a ≤ σ) (hσ' : σ ≤ b) (t : ℝ) :
      ‖f (line σ t)‖ ≤ (B * C * D ^ σ) / (1 + t ^ 2) := by
    let z := line σ t
    have hz : a ≤ z.re := (hRe σ t).symm ▸ hσ
    have hz' : z.re ≤ b := (hRe σ t).symm ▸ hσ'
    let x : ℝ := 1 + |t|
    have hx : 0 < x := by dsimp [x]; positivity
    have hx1 : 1 ≤ x := by dsimp [x]; linarith [abs_nonneg t]
    have hg : ‖Complex.Gamma z‖ ≤ B / x ^ (n + 2) := by simpa [z,hIm,x] using hG z hz hz'
    have hr : ‖R z‖ ≤ C * x ^ n := by
      have hzM : ‖R z‖ ≤ C * x ^ M := by simpa [z,hIm,x] using hM z hz hz'
      apply hzM.trans
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx1 hn
    have hc : ‖(D : ℂ) ^ z‖ = D ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hDp, hRe]
    have hx2 : 1+t^2 ≤ x^2 := by dsimp [x]; nlinarith [sq_abs t, abs_nonneg t]
    change ‖Complex.Gamma z * (D : ℂ) ^ z * R z‖ ≤ _
    rw [norm_mul, norm_mul, hc]
    calc
      _ ≤ (B / x ^ (n+2) * D ^ σ) * (C * x^n) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hDp.le _)) hr
          (norm_nonneg _) (by positivity)
      _ = (B * C * D ^ σ) / x ^ 2 := by
        rw [pow_add]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hx2
  have hInt (σ : ℝ) (hσ : a ≤ σ) (hσ' : σ ≤ b) : Integrable (fun t : ℝ => f (line σ t)) := by
    have hc : Continuous (fun t : ℝ => f (line σ t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      apply (hdiff (line σ t) (by simpa [hRe] using hσ) (by simpa [hRe] using hσ')).continuousAt.comp
      dsimp [line]
      fun_prop
    refine (integrable_inv_one_add_sq.const_mul (B*C*D^σ)).mono' hc.aestronglyMeasurable ?_
    exact ae_of_all _ fun t => by simpa only [div_eq_mul_inv] using hpoint σ hσ hσ' t
  have heq := OAI.VerticalContourShift.integral_eq_of_strip_decay f a b (B*C*D^b) hab
    hdiff (hInt a le_rfl hab) (hInt b hab le_rfl) (by
      intro σ hσ t
      refine (hpoint σ hσ.1 hσ.2 t).trans ?_
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD hσ.2) (by positivity))
        (by positivity))
  have hnorm : ‖∫ t : ℝ, f (line a t)‖ ≤ B*C*D^a * Real.pi := by
    refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul (B*C*D^a))
      (ae_of_all _ fun t => ?_)).trans_eq ?_
    · simpa only [div_eq_mul_inv] using hpoint a le_rfl hab t
    · rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [hinv D hD]
  change ‖k * ∫ t : ℝ, f (line b t)‖ ≤ _
  rw [show (∫ t : ℝ, f (line b t)) = ∫ t : ℝ, f (line a t) from heq.symm, norm_mul]
  calc
    _ ≤ ‖k‖ * (B*C*D^a*Real.pi) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hDp.le a]
