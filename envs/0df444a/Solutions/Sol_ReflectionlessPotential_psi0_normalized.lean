-- Prove2me | solution 1 for ReflectionlessPotential.psi0_normalized
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:48:39.330154+00:00
-- url     : https://prove2.me/submissions/cbd850c2-eace-47e3-b5e1-22b3051d9a1d

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology
open ReflectionlessPotential

theorem W2c_ReflectionlessPotential_tanh_deriv (κ x : ℝ) :
    HasDerivAt (fun y => Real.tanh (κ * y))
      (κ / (Real.cosh (κ * x) * Real.cosh (κ * x))) x := by
  have hc : Real.cosh (κ * x) ≠ 0 := (Real.cosh_pos _).ne'
  have hfun : (fun y => Real.tanh (κ * y)) = fun y => Real.sinh (κ * y) / Real.cosh (κ * y) :=
    funext fun y => Real.tanh_eq_sinh_div_cosh _
  have h := (((hasDerivAt_id' x).const_mul κ).sinh).div (((hasDerivAt_id' x).const_mul κ).cosh) hc
  rw [hfun]
  refine h.congr_deriv ?_
  rw [div_eq_div_iff (pow_ne_zero 2 hc) (mul_ne_zero hc hc)]
  linear_combination (κ * Real.cosh (κ * x) ^ 2) * Real.cosh_sq_sub_sinh_sq (κ * x)

theorem W2c_ReflectionlessPotential_sech2_deriv (κ x : ℝ) :
    HasDerivAt (fun y => κ / (Real.cosh (κ * y) * Real.cosh (κ * y)))
      (-(2 * κ ^ 2) * Real.tanh (κ * x) / (Real.cosh (κ * x) * Real.cosh (κ * x))) x := by
  have hc : Real.cosh (κ * x) ≠ 0 := (Real.cosh_pos _).ne'
  have hC := ((hasDerivAt_id' x).const_mul κ).cosh
  have h := (hasDerivAt_const x κ).div (hC.mul hC) (mul_ne_zero hc hc)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

theorem W2c_ReflectionlessPotential_psi0_deriv (κ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    HasDerivAt (psi0 κ) (-(κ * Real.tanh (κ * x)) * psi0 κ x) x := by
  have hc : Real.cosh (κ * x) ≠ 0 := (Real.cosh_pos _).ne'
  have h := (hasDerivAt_const x (Real.sqrt (κ / 2))).div
    (((hasDerivAt_id' x).const_mul κ).cosh) hc
  have hfun : psi0 κ = fun y => Real.sqrt (κ / 2) / Real.cosh (κ * y) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

theorem W2c_ReflectionlessPotential_sech_tanh (y : ℝ) :
    Real.tanh y ^ 2 + 1 / (Real.cosh y * Real.cosh y) = 1 := by
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos _).ne'
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, ← sq, ← add_div, ← Real.cosh_sq,
    div_self (pow_ne_zero 2 hc)]

theorem W2c_ReflectionlessPotential_psi0_eigen (κ : ℝ) (hκ : 0 < κ) :
    IsEigenstate κ (-(κ ^ 2 / 2)) (fun x => (psi0 κ x : ℂ)) := by
  have hg : ∀ x, HasDerivAt (fun y => -(κ * Real.tanh (κ * y)) * psi0 κ y)
      (-(κ * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x)))) * psi0 κ x +
        -(κ * Real.tanh (κ * x)) * (-(κ * Real.tanh (κ * x)) * psi0 κ x)) x :=
    fun x => ((W2c_ReflectionlessPotential_tanh_deriv κ x).const_mul κ).neg.mul
      (W2c_ReflectionlessPotential_psi0_deriv κ hκ x)
  refine ⟨fun x => ((-(κ * Real.tanh (κ * x)) * psi0 κ x : ℝ) : ℂ),
    fun x => ((-(κ * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x)))) * psi0 κ x +
        -(κ * Real.tanh (κ * x)) * (-(κ * Real.tanh (κ * x)) * psi0 κ x) : ℝ) : ℂ),
    fun x => (W2c_ReflectionlessPotential_psi0_deriv κ hκ x).ofReal_comp,
    fun x => (hg x).ofReal_comp, fun x => ?_⟩
  have key := W2c_ReflectionlessPotential_sech_tanh (κ * x)
  have hR : -(1 / 2) * (-(κ * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x)))) * psi0 κ x +
        -(κ * Real.tanh (κ * x)) * (-(κ * Real.tanh (κ * x)) * psi0 κ x)) +
      V κ x * psi0 κ x = -(κ ^ 2 / 2) * psi0 κ x := by
    unfold V
    linear_combination (-(κ ^ 2 / 2) * psi0 κ x) * key
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
  beta_reduce at hC ⊢
  push_cast at hC ⊢
  linear_combination hC

theorem W2c_ReflectionlessPotential_psiC_eigen (κ k : ℝ) (hκ : 0 < κ) :
    IsEigenstate κ (k ^ 2 / 2) (psiC κ k) := by
  set D : ℂ := (Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k) with hD
  have hx : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := fun x => by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hE : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * k * y))
      (Complex.exp (Complex.I * k * x) * (Complex.I * k * 1)) x :=
    fun x => ((hx x).const_mul (Complex.I * k)).cexp
  have hT : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((Real.tanh (κ * y) : ℝ) : ℂ))
      (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) x :=
    fun x => (W2c_ReflectionlessPotential_tanh_deriv κ x).ofReal_comp
  have hT2 : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ((κ / (Real.cosh (κ * y) * Real.cosh (κ * y)) : ℝ) : ℂ))
      (((-(2 * κ ^ 2) * Real.tanh (κ * x) / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ))
      x := fun x => (W2c_ReflectionlessPotential_sech2_deriv κ x).ofReal_comp
  have h1 : ∀ x : ℝ, HasDerivAt (psiC κ k)
      ((Complex.exp (Complex.I * k * x) * (Complex.I * k * 1) *
          ((k : ℂ) + Complex.I * κ * ((Real.tanh (κ * x) : ℝ) : ℂ)) +
        Complex.exp (Complex.I * k * x) *
          (Complex.I * κ * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)))) / D) x :=
    fun x => ((hE x).mul (((hT x).const_mul (Complex.I * κ)).const_add (k : ℂ))).div_const D
  have h2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ =>
      (Complex.exp (Complex.I * k * y) * (Complex.I * k * 1) *
          ((k : ℂ) + Complex.I * κ * ((Real.tanh (κ * y) : ℝ) : ℂ)) +
        Complex.exp (Complex.I * k * y) *
          (Complex.I * κ * (((κ / (Real.cosh (κ * y) * Real.cosh (κ * y)) : ℝ) : ℂ)))) / D)
      ((Complex.exp (Complex.I * k * x) * (Complex.I * k * 1) * (Complex.I * k * 1) *
          ((k : ℂ) + Complex.I * κ * ((Real.tanh (κ * x) : ℝ) : ℂ)) +
        Complex.exp (Complex.I * k * x) * (Complex.I * k * 1) *
          (Complex.I * κ * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ))) +
        (Complex.exp (Complex.I * k * x) * (Complex.I * k * 1) *
          (Complex.I * κ * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ))) +
        Complex.exp (Complex.I * k * x) * (Complex.I * κ *
          (((-(2 * κ ^ 2) * Real.tanh (κ * x) / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ)
            : ℂ))))) / D) x :=
    fun x => ((((hE x).mul_const (Complex.I * k * 1)).mul
      (((hT x).const_mul (Complex.I * κ)).const_add (k : ℂ))).add
      ((hE x).mul ((hT2 x).const_mul (Complex.I * κ)))).div_const D
  refine ⟨_, _, h1, h2, fun x => ?_⟩
  have hV : ((V κ x : ℝ) : ℂ) =
      -(κ : ℂ) * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) := by
    unfold V; push_cast; ring
  have hT'' : (((-(2 * κ ^ 2) * Real.tanh (κ * x) /
      (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) =
      -2 * (κ : ℂ) * ((Real.tanh (κ * x) : ℝ) : ℂ) *
        (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) := by
    push_cast; ring
  have hk : (((k ^ 2 / 2 : ℝ)) : ℂ) = (k : ℂ) ^ 2 / 2 := by push_cast; ring
  beta_reduce
  rw [hV, hT'', hk]
  unfold psiC
  rw [← hD]
  generalize (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) = S
  generalize ((Real.tanh (κ * x) : ℝ) : ℂ) = T
  generalize Complex.exp (Complex.I * k * x) = E
  linear_combination (-(1 / 2) * (E / D) * ((k : ℂ) ^ 3 + Complex.I * (k : ℂ) ^ 2 * κ * T +
    2 * k * κ * S)) * Complex.I_sq

theorem W2c_ReflectionlessPotential_creation (κ E : ℝ) (hκ : 0 < κ) (f f' : ℝ → ℂ)
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : IsFreeEigenstate E f) :
    IsEigenstate κ E (creation κ f f') := by
  obtain ⟨g', g'', hg', hg'', heq⟩ := hf
  have hgf : g' = f' := funext fun x => (hg' x).unique (hf' x)
  have hf'' : ∀ x, HasDerivAt f' (g'' x) x := by rw [← hgf]; exact hg''
  have hg2 : ∀ x, g'' x = -2 * (E : ℂ) * f x := by
    intro x; have := heq x; linear_combination (-2 : ℂ) * this
  have hg2d : ∀ x, HasDerivAt g'' (-2 * (E : ℂ) * f' x) x := by
    intro x
    have : g'' = fun y => -2 * (E : ℂ) * f y := funext hg2
    rw [this]
    exact (hf' x).const_mul _
  have hT : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((Real.tanh (κ * y) : ℝ) : ℂ))
      (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) x :=
    fun x => (W2c_ReflectionlessPotential_tanh_deriv κ x).ofReal_comp
  have hT2 : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ((κ / (Real.cosh (κ * y) * Real.cosh (κ * y)) : ℝ) : ℂ))
      (((-(2 * κ ^ 2) * Real.tanh (κ * x) / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ))
      x := fun x => (W2c_ReflectionlessPotential_sech2_deriv κ x).ofReal_comp
  have h1 : ∀ x, HasDerivAt (creation κ f f')
      ((-Complex.I * g'' x + (Complex.I * κ *
          (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) * f x +
        Complex.I * κ * ((Real.tanh (κ * x) : ℝ) : ℂ) * f' x)) / (Real.sqrt 2 : ℂ)) x :=
    fun x => (((hf'' x).const_mul (-Complex.I)).add
      (((hT x).const_mul (Complex.I * κ)).mul (hf' x))).div_const _
  have h2 : ∀ x, HasDerivAt (fun y => (-Complex.I * g'' y + (Complex.I * κ *
          (((κ / (Real.cosh (κ * y) * Real.cosh (κ * y)) : ℝ) : ℂ)) * f y +
        Complex.I * κ * ((Real.tanh (κ * y) : ℝ) : ℂ) * f' y)) / (Real.sqrt 2 : ℂ))
      ((-Complex.I * (-2 * (E : ℂ) * f' x) +
        ((Complex.I * κ * (((-(2 * κ ^ 2) * Real.tanh (κ * x) /
            (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) * f x +
          Complex.I * κ * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) * f' x) +
        (Complex.I * κ * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) * f' x +
          Complex.I * κ * ((Real.tanh (κ * x) : ℝ) : ℂ) * g'' x))) / (Real.sqrt 2 : ℂ)) x :=
    fun x => (((hg2d x).const_mul (-Complex.I)).add
      ((((hT2 x).const_mul (Complex.I * κ)).mul (hf' x)).add
        (((hT x).const_mul (Complex.I * κ)).mul (hf'' x)))).div_const _
  refine ⟨_, _, h1, h2, fun x => ?_⟩
  have hV : ((V κ x : ℝ) : ℂ) =
      -(κ : ℂ) * (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) := by
    unfold V; push_cast; ring
  have hT'' : (((-(2 * κ ^ 2) * Real.tanh (κ * x) /
      (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) =
      -2 * (κ : ℂ) * ((Real.tanh (κ * x) : ℝ) : ℂ) *
        (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) := by
    push_cast; ring
  beta_reduce
  rw [hV, hT'', hg2 x]
  unfold creation
  generalize (((κ / (Real.cosh (κ * x) * Real.cosh (κ * x)) : ℝ) : ℂ)) = S
  generalize ((Real.tanh (κ * x) : ℝ) : ℂ) = T
  ring

theorem W2c_ReflectionlessPotential_recovery (κ : ℝ) (hκ : 0 < κ) (g : ℝ → ℂ)
    (hg : ∀ x y : ℝ, (starRingEnd ℂ) (g x) * g y =
      ((κ / (2 * Real.cosh (κ * x) * Real.cosh (κ * y)) : ℝ) : ℂ)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, g x = c * psi0 κ x := by
  have hs : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (by positivity)
  have h00 := hg 0 0
  simp only [mul_zero, Real.cosh_zero, mul_one] at h00
  have hn : ‖g 0‖ ^ 2 = κ / 2 := by
    rw [Complex.conj_mul'] at h00
    exact_mod_cast h00
  have hn' : ‖g 0‖ = Real.sqrt (κ / 2) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨g 0 / (Real.sqrt (κ / 2) : ℂ), ?_, fun y => ?_⟩
  · rw [norm_div, hn', Complex.norm_real, Real.norm_of_nonneg hs.le, div_self hs.ne']
  · have hy := hg 0 y
    simp only [mul_zero, Real.cosh_zero, mul_one] at hy
    have hc := Real.cosh_pos (κ * y)
    have e1 : ((κ / 2 : ℝ) : ℂ) * g y = g 0 * ((κ / (2 * Real.cosh (κ * y)) : ℝ) : ℂ) := by
      rw [← h00, ← hy]; ring
    unfold psi0
    generalize Real.cosh (κ * y) = C at hc e1 ⊢
    generalize Real.sqrt (κ / 2) = s at hs ⊢
    push_cast at e1 ⊢
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hCc : (C : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e2 : g y = g 0 / (C : ℂ) := by
      have h2 : (κ : ℂ) / 2 ≠ 0 := div_ne_zero hκc two_ne_zero
      apply mul_left_cancel₀ h2
      rw [e1]
      ring
    rw [e2]
    field_simp

theorem W2c_ReflectionlessPotential_even_odd (κ k x : ℝ) (hκ : 0 < κ) :
    psiEven κ k x =
        ((k * Real.cos (k * x) - κ * Real.sin (k * x) * Real.tanh (κ * x) : ℝ) : ℂ) /
          ((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k)) ∧
      psiOdd κ k x =
        Complex.I * ((k * Real.sin (k * x) + κ * Real.cos (k * x) * Real.tanh (κ * x) : ℝ) : ℂ) /
          ((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k)) := by
  have he : Complex.exp (Complex.I * k * x) =
      ((Real.cos (k * x) : ℝ) : ℂ) + ((Real.sin (k * x) : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * k * x = ((k * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have he' : Complex.exp (Complex.I * k * ((-x : ℝ) : ℂ)) =
      ((Real.cos (k * x) : ℝ) : ℂ) - ((Real.sin (k * x) : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * k * ((-x : ℝ) : ℂ) = ((-(k * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  have hsq : (Real.sqrt (2 * Real.pi) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  unfold psiEven psiOdd psiC
  rw [he, he', mul_neg, Real.tanh_neg, hsq]
  generalize Real.cos (k * x) = C
  generalize Real.sin (k * x) = S
  generalize Real.tanh (κ * x) = T
  have hQ : (κ : ℂ) + Complex.I * k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  have hsp : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hL : (Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k) *
      (Real.sqrt 2 : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hs2 hsp) hQ) hs2
  have hR : (Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k) ≠ 0 := mul_ne_zero hsp hQ
  constructor
  · rw [← add_div, div_div, div_eq_div_iff hL hR]
    push_cast
    linear_combination ((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k) * 2 * S * κ * T) *
      Complex.I_sq - ((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k) *
        (k * C - κ * S * T)) * h2
  · rw [← sub_div, div_div, div_eq_div_iff hL hR]
    push_cast
    linear_combination (-((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k)) * Complex.I *
      (k * S + κ * C * T)) * h2

theorem W2c_ReflectionlessPotential_tanh_top : Tendsto Real.tanh atTop (𝓝 1) := by
  have e : ∀ x, Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
    intro x
    have hE := Real.exp_pos x
    have hE' := hE.ne'
    have hE2 : Real.exp x ^ 2 + 1 ≠ 0 := by positivity
    have h2 : Real.exp (2 * x) = Real.exp x ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, h2]
    field_simp
    ring
  have h : Tendsto (fun x => 1 - 2 / (Real.exp (2 * x) + 1)) atTop (𝓝 (1 - 0)) := by
    apply tendsto_const_nhds.sub
    apply tendsto_const_nhds.div_atTop
    apply tendsto_atTop_add_const_right
    exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos)
  rw [sub_zero] at h
  exact h.congr (fun x => (e x).symm)

theorem W2c_ReflectionlessPotential_tanh_bot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have h := W2c_ReflectionlessPotential_tanh_top.comp tendsto_neg_atBot_atTop
  have h2 := h.neg
  refine h2.congr (fun x => ?_)
  simp [Real.tanh_neg]

theorem W2c_ReflectionlessPotential_reflectionless (κ k : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => psiC κ k x -
        Complex.exp (Complex.I * k * x) * (((k : ℂ) - Complex.I * κ) /
          ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k)))) atBot (𝓝 0) ∧
      Tendsto (fun x : ℝ => psiC κ k x -
        Complex.exp (Complex.I * k * x) * (((k : ℂ) + Complex.I * κ) /
          ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k)))) atTop (𝓝 0) ∧
      ‖((k : ℂ) - Complex.I * κ) / ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k))‖ =
        ‖((k : ℂ) + Complex.I * κ) /
          ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k))‖ := by
  set Z : ℂ := (Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k) with hZ
  set c : ℂ := Complex.I * κ / Z with hc
  have hEn : ∀ x : ℝ, ‖Complex.exp (Complex.I * k * x)‖ = 1 := by
    intro x
    rw [show Complex.I * k * x = ((k * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnorm : ∀ x : ℝ, ∀ s : ℝ, ‖c * Complex.exp (Complex.I * k * x) *
      (((Real.tanh (κ * x) : ℝ) : ℂ) + (s : ℂ))‖ = ‖c‖ * |Real.tanh (κ * x) + s| := by
    intro x s
    rw [norm_mul, norm_mul, hEn, mul_one,
      show (((Real.tanh (κ * x) : ℝ) : ℂ) + (s : ℂ)) = ((Real.tanh (κ * x) + s : ℝ) : ℂ) by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  refine ⟨?_, ?_, ?_⟩
  · have hd : ∀ x : ℝ, psiC κ k x - Complex.exp (Complex.I * k * x) * (((k : ℂ) -
        Complex.I * κ) / Z) = c * Complex.exp (Complex.I * k * x) *
          (((Real.tanh (κ * x) : ℝ) : ℂ) + ((1 : ℝ) : ℂ)) := by
      intro x; unfold psiC; rw [← hZ, hc]; push_cast; ring
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hl := ((W2c_ReflectionlessPotential_tanh_bot.comp
      (tendsto_id.const_mul_atBot hκ)).add_const 1).abs.const_mul ‖c‖
    simp only [neg_add_cancel, abs_zero, mul_zero] at hl
    refine hl.congr (fun x => ?_)
    beta_reduce
    rw [hd x, hnorm x 1]
    simp
  · have hd : ∀ x : ℝ, psiC κ k x - Complex.exp (Complex.I * k * x) * (((k : ℂ) +
        Complex.I * κ) / Z) = c * Complex.exp (Complex.I * k * x) *
          (((Real.tanh (κ * x) : ℝ) : ℂ) + ((-1 : ℝ) : ℂ)) := by
      intro x; unfold psiC; rw [← hZ, hc]; push_cast; ring
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hl := ((W2c_ReflectionlessPotential_tanh_top.comp
      (tendsto_id.const_mul_atTop hκ)).add_const (-1)).abs.const_mul ‖c‖
    simp only [add_neg_cancel, abs_zero, mul_zero] at hl
    refine hl.congr (fun x => ?_)
    beta_reduce
    rw [hd x, hnorm x (-1)]
    simp
  · rw [norm_div, norm_div]
    congr 1
    have : (k : ℂ) - Complex.I * κ = (starRingEnd ℂ) ((k : ℂ) + Complex.I * κ) := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [this, Complex.norm_conj]

theorem W2c_ReflectionlessPotential_normalized (κ : ℝ) (hκ : 0 < κ) :
    ∫ x : ℝ, psi0 κ x ^ 2 = 1 := by
  have hc : ∀ x, Real.cosh (κ * x) ≠ 0 := fun x => (Real.cosh_pos _).ne'
  have hf : ∀ x, HasDerivAt (fun y => (1 / 2 : ℝ) * Real.tanh (κ * y))
      ((1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x)))) x :=
    fun x => (W2c_ReflectionlessPotential_tanh_deriv κ x).const_mul (1 / 2)
  have hfeq : (fun x => psi0 κ x ^ 2) =
      fun x => (1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x))) := by
    funext x
    unfold psi0
    rw [div_pow, Real.sq_sqrt (by positivity)]
    have := hc x
    field_simp
    try ring
  have hcont : Continuous fun x => (1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x))) :=
    continuous_const.mul (continuous_const.div (by fun_prop)
      (fun x => mul_ne_zero (hc x) (hc x)))
  have hnn : ∀ x, 0 ≤ (1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x))) :=
    fun x => by have := Real.cosh_pos (κ * x); positivity
  have hint : Integrable fun x => (1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x))) := by
    refine integrable_of_intervalIntegral_norm_bounded (l := atTop) (a := fun i : ℝ => -i)
      (b := fun i : ℝ => i) 1 (fun i => hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      tendsto_neg_atTop_atBot tendsto_id ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with i hi
    have e : ∫ x in (-i)..i, ‖(1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x)))‖ =
        (1 / 2 : ℝ) * Real.tanh (κ * i) - (1 / 2 : ℝ) * Real.tanh (κ * -i) := by
      rw [intervalIntegral.integral_congr (g := fun x =>
        (1 / 2 : ℝ) * (κ / (Real.cosh (κ * x) * Real.cosh (κ * x))))
        (fun x _ => Real.norm_of_nonneg (hnn x))]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
        (hcont.intervalIntegrable _ _)
    rw [e]
    have h1 := Real.tanh_lt_one (κ * i)
    have h2 := Real.neg_one_lt_tanh (κ * -i)
    linarith
  have htop : Tendsto (fun y => (1 / 2 : ℝ) * Real.tanh (κ * y)) atTop (𝓝 ((1 / 2 : ℝ) * 1)) :=
    (W2c_ReflectionlessPotential_tanh_top.comp (tendsto_id.const_mul_atTop hκ)).const_mul _
  have hbot : Tendsto (fun y => (1 / 2 : ℝ) * Real.tanh (κ * y)) atBot
      (𝓝 ((1 / 2 : ℝ) * (-1))) :=
    (W2c_ReflectionlessPotential_tanh_bot.comp (tendsto_id.const_mul_atBot hκ)).const_mul _
  rw [hfeq, integral_of_hasDerivAt_of_tendsto hf hint hbot htop]
  norm_num

theorem solution (κ : ℝ) (hκ : 0 < κ) : ∫ x : ℝ, psi0 κ x ^ 2 = 1 := by
  apply W2c_ReflectionlessPotential_normalized <;> assumption
