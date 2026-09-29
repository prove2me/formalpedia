-- Prove2me | solution 1 for ReflectionlessPotential.parity_spectral_weight
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:40:06.329047+00:00
-- url     : https://prove2.me/submissions/2f3c98a4-82a1-492c-b2b2-9f529c3ccff6

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology
open ReflectionlessPotential

/-- For a nonnegative continuous `h`, `∫_{k>0} (h k + h (-k)) = ∫ h`. -/
theorem W7b_ReflectionlessPotential_split (h : ℝ → ℝ) (hc : Continuous h) (hnn : ∀ k, 0 ≤ h k) :
    ∫ k in Set.Ioi (0 : ℝ), (h k + h (-k)) = ∫ k, h k := by
  set g : ℝ → ℝ := fun k => h k + h (-k) with hg
  have heven : ∀ x, g |x| = g x := by
    intro x
    rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
    · rw [hx]
    · rw [hx]; simp only [hg, neg_neg]; ring
  have habs := integral_comp_abs (f := g)
  simp_rw [heven] at habs
  have hIoi : ∫ k in Set.Ioi (0 : ℝ), g k = (∫ k, g k) / 2 := by rw [habs]; ring
  show ∫ k in Set.Ioi (0 : ℝ), g k = _
  rw [hIoi]
  by_cases hi : Integrable h
  · have hi' : Integrable (fun k => h (-k)) := hi.comp_neg
    rw [hg, integral_add hi hi', integral_neg_eq_self (fun k => h k)]
    ring
  · rw [integral_undef hi]
    have : ¬ Integrable g := by
      intro hgi
      apply hi
      refine hgi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun k => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn k)]
      simp only [hg]; linarith [hnn (-k)]
    rw [integral_undef this]; simp

theorem W7b_ReflectionlessPotential_den_ne (κ k : ℝ) (hκ : 0 < κ) :
    (κ : ℂ) + Complex.I * k ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this; linarith

theorem W7b_ReflectionlessPotential_den_ne' (κ k : ℝ) (hκ : 0 < κ) :
    (κ : ℂ) - Complex.I * k ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this; linarith

/-- The reflection identity `ψ_k(-x) = ω(k) ψ_{-k}(x)`. -/
theorem W7b_ReflectionlessPotential_psi_neg (κ k x : ℝ) (hκ : 0 < κ) :
    psiC κ k (-x) = -(((κ : ℂ) - Complex.I * k) / ((κ : ℂ) + Complex.I * k)) * psiC κ (-k) x := by
  have h1 := W7b_ReflectionlessPotential_den_ne κ k hκ
  have h2 := W7b_ReflectionlessPotential_den_ne' κ k hκ
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  unfold psiC
  have he : Complex.exp (Complex.I * (k : ℂ) * ((-x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((-k : ℝ) : ℂ) * (x : ℂ)) := by
    congr 1; push_cast; ring
  rw [he, show κ * -x = -(κ * x) by ring, Real.tanh_neg, Complex.ofReal_neg, Complex.ofReal_neg,
    show (κ : ℂ) + Complex.I * -(k : ℂ) = (κ : ℂ) - Complex.I * k by ring]
  have key : ∀ R : ℂ, -(((κ : ℂ) - Complex.I * k) / ((κ : ℂ) + Complex.I * k)) *
      (R / ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) - Complex.I * k))) =
      -R / ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k)) := by
    intro R; field_simp
  rw [key]
  congr 1
  ring

theorem W7b_ReflectionlessPotential_norm_omega (κ k : ℝ) (hκ : 0 < κ) :
    ‖-(((κ : ℂ) - Complex.I * k) / ((κ : ℂ) + Complex.I * k))‖ = 1 := by
  rw [norm_neg, norm_div]
  have : ‖(κ : ℂ) - Complex.I * k‖ = ‖(κ : ℂ) + Complex.I * k‖ := by
    rw [← Complex.norm_conj]; congr 1; simp [Complex.conj_ofReal] <;> ring
  rw [this, div_self]
  exact norm_ne_zero_iff.mpr (W7b_ReflectionlessPotential_den_ne κ k hκ)

theorem W7b_ReflectionlessPotential_tanh_cont (κ : ℝ) :
    Continuous (fun x : ℝ => Real.tanh (κ * x)) := by
  have : (fun x : ℝ => Real.tanh (κ * x)) = fun x => Real.sinh (κ * x) / Real.cosh (κ * x) := by
    funext x; rw [Real.tanh_eq_sinh_div_cosh]
  rw [this]
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => (Real.cosh_pos _).ne')

theorem W7b_ReflectionlessPotential_psi_cont_x (κ k : ℝ) (hκ : 0 < κ) :
    Continuous (fun x => psiC κ k x) := by
  unfold psiC
  have ht := W7b_ReflectionlessPotential_tanh_cont κ
  apply Continuous.div (by fun_prop) continuous_const
  intro x
  apply mul_ne_zero
  · have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  · exact W7b_ReflectionlessPotential_den_ne κ k hκ

theorem W7b_ReflectionlessPotential_psi_cont_k (κ x : ℝ) (hκ : 0 < κ) :
    Continuous (fun k => psiC κ k x) := by
  unfold psiC
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro k
  apply mul_ne_zero
  · have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  · exact W7b_ReflectionlessPotential_den_ne κ k hκ

theorem W7b_ReflectionlessPotential_conj_cont (κ k : ℝ) (hκ : 0 < κ) :
    Continuous (fun x => (starRingEnd ℂ) (psiC κ k x)) :=
  Complex.continuous_conj.comp (W7b_ReflectionlessPotential_psi_cont_x κ k hκ)

theorem W7b_ReflectionlessPotential_conj_cont_neg (κ k : ℝ) (hκ : 0 < κ) :
    Continuous (fun x => (starRingEnd ℂ) (psiC κ k (-x))) :=
  Complex.continuous_conj.comp ((W7b_ReflectionlessPotential_psi_cont_x κ k hκ).comp continuous_neg)

theorem W7b_ReflectionlessPotential_psi_bound (κ k x : ℝ) (hκ : 0 < κ) :
    ‖psiC κ k x‖ ≤ 2 := by
  unfold psiC
  rw [norm_div, norm_mul, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (k : ℂ) * (x : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero, one_mul]
  have hs : 1 ≤ ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hnum : ‖(k : ℂ) + Complex.I * κ * Real.tanh (κ * x)‖ ≤ |k| + κ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    gcongr
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hκ]
    have : |Real.tanh (κ * x)| ≤ 1 := by
      rw [abs_le]; constructor
      · linarith [Real.neg_one_lt_tanh (κ * x)]
      · linarith [Real.tanh_lt_one (κ * x)]
    nlinarith [abs_nonneg (Real.tanh (κ * x))]
  have hden : (|k| + κ) / 2 ≤ ‖(κ : ℂ) + Complex.I * k‖ := by
    have e : (κ : ℂ) + Complex.I * k = ⟨κ, k⟩ := by apply Complex.ext <;> simp
    rw [e, Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs k, abs_nonneg k]
  have hdpos : 0 < ‖(κ : ℂ) + Complex.I * k‖ :=
    norm_pos_iff.mpr (W7b_ReflectionlessPotential_den_ne κ k hκ)
  rw [div_le_iff₀ (by positivity)]
  calc ‖(k : ℂ) + Complex.I * κ * Real.tanh (κ * x)‖ ≤ |k| + κ := hnum
    _ ≤ 2 * ‖(κ : ℂ) + Complex.I * k‖ := by linarith
    _ ≤ 2 * (‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)‖ * ‖(κ : ℂ) + Complex.I * k‖) := by
        nlinarith

theorem W7b_ReflectionlessPotential_integrable (κ k : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable (fun x => g x * f x) := by
  apply Continuous.integrable_of_hasCompactSupport (hg.mul hf)
  exact hsupp.mul_left

theorem W7b_ReflectionlessPotential_coeff_cont (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    Continuous (fun k => coeffC κ k f) := by
  unfold coeffC
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hsupp
  apply continuous_of_dominated (bound := fun x => 2 * ‖f x‖)
  · intro k
    exact ((W7b_ReflectionlessPotential_conj_cont κ k hκ).mul hf).aestronglyMeasurable
  · intro k
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (W7b_ReflectionlessPotential_psi_bound κ k x hκ) (norm_nonneg _)
  · exact hfi.norm.const_mul 2
  · refine Eventually.of_forall fun x => ?_
    exact (Complex.continuous_conj.comp (W7b_ReflectionlessPotential_psi_cont_k κ x hκ)).mul
      continuous_const

theorem W7b_ReflectionlessPotential_pointwise (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) (k : ℝ) :
    ‖coeffEven κ k f‖ ^ 2 + ‖coeffOdd κ k f‖ ^ 2 =
      ‖coeffC κ k f‖ ^ 2 + ‖coeffC κ (-k) f‖ ^ 2 := by
  have hc1 := W7b_ReflectionlessPotential_conj_cont κ k hκ
  have hc2 := W7b_ReflectionlessPotential_conj_cont_neg κ k hκ
  have i1 := W7b_ReflectionlessPotential_integrable κ k hκ f hf hsupp _ hc1
  have i2 := W7b_ReflectionlessPotential_integrable κ k hκ f hf hsupp _ hc2
  have hdc : (∫ x, (starRingEnd ℂ) (psiC κ k (-x)) * f x) =
      (starRingEnd ℂ) (-(((κ : ℂ) - Complex.I * k) / ((κ : ℂ) + Complex.I * k))) *
        coeffC κ (-k) f := by
    rw [coeffC, ← integral_const_mul]
    congr 1; funext x
    rw [W7b_ReflectionlessPotential_psi_neg κ k x hκ, map_mul]; ring
  have hE : coeffEven κ k f =
      (coeffC κ k f + ∫ x, (starRingEnd ℂ) (psiC κ k (-x)) * f x) / (Real.sqrt 2 : ℂ) := by
    unfold coeffEven psiEven coeffC
    rw [← integral_add i1 i2, ← integral_div]
    congr 1; funext x
    rw [map_div₀, Complex.conj_ofReal, map_add]; ring
  have hO : coeffOdd κ k f =
      (coeffC κ k f - ∫ x, (starRingEnd ℂ) (psiC κ k (-x)) * f x) / (Real.sqrt 2 : ℂ) := by
    unfold coeffOdd psiOdd coeffC
    rw [← integral_sub i1 i2, ← integral_div]
    congr 1; funext x
    rw [map_div₀, Complex.conj_ofReal, map_sub]; ring
  set c := coeffC κ k f
  set d := ∫ x, (starRingEnd ℂ) (psiC κ k (-x)) * f x with hd
  have hdn : ‖d‖ = ‖coeffC κ (-k) f‖ := by
    rw [hdc, norm_mul, Complex.norm_conj, W7b_ReflectionlessPotential_norm_omega κ k hκ, one_mul]
  have hpar := parallelogram_law_with_norm ℝ c d
  have hn2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  rw [hE, hO, norm_div, norm_div, div_pow, div_pow, hn2, ← hdn]
  have hn : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := hn2
  nlinarith [hpar]

theorem solution (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    (∫ k in Set.Ioi (0 : ℝ), (‖coeffEven κ k f‖ ^ 2 + ‖coeffOdd κ k f‖ ^ 2)) =
      ∫ k : ℝ, ‖coeffC κ k f‖ ^ 2 := by
  simp_rw [W7b_ReflectionlessPotential_pointwise κ hκ f hf hsupp]
  exact W7b_ReflectionlessPotential_split (fun k => ‖coeffC κ k f‖ ^ 2)
    ((W7b_ReflectionlessPotential_coeff_cont κ hκ f hf hsupp).norm.pow 2)
    (fun k => sq_nonneg _)
