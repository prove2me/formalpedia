-- Prove2me | solution 1 for Pendulum.harmonic_solution
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:50:18.338396+00:00
-- url     : https://prove2.me/submissions/a9744535-2b9b-4c5e-8439-49ea9339ade6

import Mathlib
import Definitions.Def_PendulumDefs

open Pendulum

theorem W2m_Pendulum_energy_constant (g l : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsMotion g l theta omega alpha) (t : ℝ) :
    energy g l theta omega t = energy g l theta omega 0 := by
  have hd : ∀ s, HasDerivAt (energy g l theta omega) 0 s := by
    intro s
    show HasDerivAt (fun t => omega t ^ 2 / 2 - (g / l) * Real.cos (theta t)) 0 s
    have h1 := ((h.hasDerivAt_omega s).fun_pow 2).div_const 2
    have h2 := ((h.hasDerivAt_theta s).cos).const_mul (g / l)
    refine (h1.fun_sub h2).congr_deriv ?_
    rw [h.equation s]
    first | ring1 | (norm_num; ring1) | (simp; ring1) | simp
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

theorem W2m_Pendulum_sq_angularVelocity_eq (g l theta0 : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsMotion g l theta omega alpha) (hinit : theta 0 = theta0) (hrest : omega 0 = 0)
    (t : ℝ) :
    omega t ^ 2 = 2 * (g / l) * (Real.cos (theta t) - Real.cos theta0) := by
  have H := W2m_Pendulum_energy_constant g l theta omega alpha h t
  simp only [energy, hinit, hrest] at H
  linear_combination 2 * H

theorem W2m_Pendulum_harmonic_solution (w theta0 : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion w theta omega alpha) (hinit : theta 0 = theta0)
    (hrest : omega 0 = 0) :
    ∀ t, theta t = theta0 * Real.cos (w * t) := by
  set e : ℝ → ℝ := fun t => theta t - theta0 * Real.cos (w * t) with he
  set e' : ℝ → ℝ := fun t => omega t + theta0 * w * Real.sin (w * t) with he'
  have hde : ∀ t, HasDerivAt e (e' t) t := by
    intro t
    have h1 := (((hasDerivAt_id' t).const_mul w).cos).const_mul theta0
    refine ((h.hasDerivAt_theta t).fun_sub h1).congr_deriv ?_
    simp only [he']
    ring
  have hde' : ∀ t, HasDerivAt e' (-(w ^ 2) * e t) t := by
    intro t
    have h1 := (((hasDerivAt_id' t).const_mul w).sin).const_mul (theta0 * w)
    refine ((h.hasDerivAt_omega t).fun_add h1).congr_deriv ?_
    rw [h.equation t]
    simp only [he]
    ring
  have hE : ∀ t, HasDerivAt (fun s => e' s ^ 2 + w ^ 2 * e s ^ 2) 0 t := by
    intro t
    refine (((hde' t).fun_pow 2).fun_add (((hde t).fun_pow 2).const_mul (w ^ 2))).congr_deriv ?_
    first | ring1 | (norm_num; ring1) | (simp; ring1) | simp
  have hc := is_const_of_deriv_eq_zero (fun s => (hE s).differentiableAt)
    (fun s => (hE s).deriv)
  have h0 : e' 0 ^ 2 + w ^ 2 * e 0 ^ 2 = 0 := by
    simp [he, he', hinit, hrest]
  have he'0 : ∀ t, e' t = 0 := by
    intro t
    have H := hc t 0
    rw [h0] at H
    have H2 : e' t ^ 2 = 0 := by
      nlinarith [sq_nonneg (e' t), mul_nonneg (sq_nonneg w) (sq_nonneg (e t))]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 H2
  intro t
  have hc2 := is_const_of_deriv_eq_zero (f := e) (fun s => (hde s).differentiableAt)
    (fun s => by rw [(hde s).deriv, he'0 s]) t 0
  have he0 : e 0 = 0 := by simp [he, hinit]
  have H : e t = 0 := hc2.trans he0
  simp only [he] at H
  linarith

theorem W2m_Pendulum_smallAngle_period (g l theta0 : ℝ) (hg : 0 < g) (hl : 0 < l)
    (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion (Real.sqrt (g / l)) theta omega alpha)
    (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    (∀ t, theta t = theta0 * Real.cos (Real.sqrt (g / l) * t)) ∧
      Function.Periodic theta (smallAnglePeriod g l) := by
  have hsol := W2m_Pendulum_harmonic_solution _ theta0 theta omega alpha h hinit hrest
  refine ⟨hsol, ?_⟩
  intro t
  rw [hsol, hsol, smallAnglePeriod]
  have hg' : g ≠ 0 := hg.ne'
  have hl' : l ≠ 0 := hl.ne'
  have h1 : Real.sqrt (g / l) * Real.sqrt (l / g) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show g / l * (l / g) = 1 by field_simp]
    simp
  have : Real.sqrt (g / l) * (t + 2 * Real.pi * Real.sqrt (l / g))
      = Real.sqrt (g / l) * t + 2 * Real.pi := by
    linear_combination (2 * Real.pi) * h1
  rw [this, Real.cos_add_two_pi]

theorem W2m_Pendulum_compound_period (m g r IO theta0 : ℝ) (hm : 0 < m) (hg : 0 < g)
    (hr : 0 < r)
    (hIO : 0 < IO) (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion (Real.sqrt (m * g * r / IO)) theta omega alpha)
    (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    Function.Periodic theta (2 * Real.pi * Real.sqrt (IO / (m * g * r))) := by
  have hsol := W2m_Pendulum_harmonic_solution _ theta0 theta omega alpha h hinit hrest
  intro t
  rw [hsol, hsol]
  have hA : m * g * r ≠ 0 := by positivity
  have hI : IO ≠ 0 := hIO.ne'
  have h1 : Real.sqrt (m * g * r / IO) * Real.sqrt (IO / (m * g * r)) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show m * g * r / IO * (IO / (m * g * r)) = 1 by field_simp]
    simp
  have : Real.sqrt (m * g * r / IO) * (t + 2 * Real.pi * Real.sqrt (IO / (m * g * r)))
      = Real.sqrt (m * g * r / IO) * t + 2 * Real.pi := by
    linear_combination (2 * Real.pi) * h1
  rw [this, Real.cos_add_two_pi]

theorem W2m_Pendulum_lipschitz (g l : ℝ) :
    LipschitzWith (Real.toNNReal (1 + |g / l|))
      (fun p : ℝ × ℝ => (p.2, -(g / l) * Real.sin p.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.coe_toNNReal _ (by positivity)]
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [Real.dist_eq]
  have h1 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have h2 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have h3 : |-(g / l) * Real.sin p.1 - -(g / l) * Real.sin q.1| ≤ |g / l| * |p.1 - q.1| := by
    rw [show -(g / l) * Real.sin p.1 - -(g / l) * Real.sin q.1
        = -(g / l) * (Real.sin p.1 - Real.sin q.1) by ring, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (abs_nonneg _)
  have hM : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := le_trans (abs_nonneg _) h1
  have h4 : |g / l| * |p.1 - q.1| ≤ |g / l| * max |p.1 - q.1| |p.2 - q.2| :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h5 : 0 ≤ |g / l| * max |p.1 - q.1| |p.2 - q.2| := mul_nonneg (abs_nonneg _) hM
  apply max_le
  · nlinarith
  · nlinarith

theorem W2m_Pendulum_motion_unique (g l : ℝ)
    (theta₁ omega₁ alpha₁ theta₂ omega₂ alpha₂ : ℝ → ℝ)
    (h₁ : IsMotion g l theta₁ omega₁ alpha₁) (h₂ : IsMotion g l theta₂ omega₂ alpha₂)
    (hθ : theta₁ 0 = theta₂ 0) (hω : omega₁ 0 = omega₂ 0) :
    theta₁ = theta₂ ∧ omega₁ = omega₂ := by
  have hLip := W2m_Pendulum_lipschitz g l
  have d1 : ∀ t, HasDerivAt (fun t => (theta₁ t, omega₁ t))
      ((fun p : ℝ × ℝ => (p.2, -(g / l) * Real.sin p.1)) (theta₁ t, omega₁ t)) t := by
    intro t
    have H := (h₁.hasDerivAt_theta t).prodMk (h₁.hasDerivAt_omega t)
    rw [h₁.equation t] at H
    exact H
  have d2 : ∀ t, HasDerivAt (fun t => (theta₂ t, omega₂ t))
      ((fun p : ℝ × ℝ => (p.2, -(g / l) * Real.sin p.1)) (theta₂ t, omega₂ t)) t := by
    intro t
    have H := (h₂.hasDerivAt_theta t).prodMk (h₂.hasDerivAt_omega t)
    rw [h₂.equation t] at H
    exact H
  have key := ODE_solution_unique_univ
    (v := fun _ p => (p.2, -(g / l) * Real.sin p.1)) (s := fun _ => Set.univ) (t₀ := 0)
    (f := fun t => (theta₁ t, omega₁ t)) (g := fun t => (theta₂ t, omega₂ t))
    (fun _ => hLip.lipschitzOnWith)
    (fun t => ⟨d1 t, Set.mem_univ _⟩) (fun t => ⟨d2 t, Set.mem_univ _⟩)
    (by simp [hθ, hω])
  exact ⟨funext fun t => congrArg Prod.fst (congrFun key t),
    funext fun t => congrArg Prod.snd (congrFun key t)⟩

theorem W2m_Pendulum_never_reaches_vertical (g l : ℝ) (hg : 0 < g) (hl : 0 < l)
    (theta omega alpha : ℝ → ℝ) (h : IsMotion g l theta omega alpha)
    (hsep : ∀ t, omega t ^ 2 = 2 * (g / l) * (1 + Real.cos (theta t)))
    (hinit : |theta 0| < Real.pi) :
    ∀ t, |theta t| < Real.pi := by
  intro t
  by_contra hcon
  push_neg at hcon
  have hcont : Continuous theta :=
    continuous_iff_continuousAt.2 fun s => (h.hasDerivAt_theta s).continuousAt
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := (0 : ℝ)) (b := t)
    (f := fun u => |theta u|) hcont.abs.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hinit.le, hcon⟩))
  have hs2 : |theta s| = Real.pi := hs
  have hs' : theta s = Real.pi ∨ theta s = -Real.pi := (abs_eq Real.pi_pos.le).1 hs2
  have hsin : Real.sin (theta s) = 0 := by rcases hs' with h' | h' <;> simp [h']
  have hcos : Real.cos (theta s) = -1 := by rcases hs' with h' | h' <;> simp [h']
  have hom : omega s = 0 := by
    have H := hsep s
    rw [hcos] at H
    exact (pow_eq_zero_iff two_ne_zero).1 (by rw [H]; ring)
  have hm1 : IsMotion g l (fun u => theta (u + s)) (fun u => omega (u + s))
      (fun u => alpha (u + s)) :=
    ⟨fun u => (h.hasDerivAt_theta (u + s)).comp_add_const u s,
     fun u => (h.hasDerivAt_omega (u + s)).comp_add_const u s,
     fun u => h.equation (u + s)⟩
  have hm2 : IsMotion g l (fun _ => theta s) (fun _ => 0) (fun _ => 0) :=
    ⟨fun u => hasDerivAt_const u _, fun u => hasDerivAt_const u _, fun u => by simp [hsin]⟩
  obtain ⟨e1, -⟩ := W2m_Pendulum_motion_unique g l _ _ _ _ _ _ hm1 hm2 (by simp)
    (by simp [hom])
  have H := congrFun e1 (-s)
  simp only [neg_add_cancel] at H
  rw [H, hs2] at hinit
  exact lt_irrefl _ hinit

theorem solution (w theta0 : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion w theta omega alpha) (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    ∀ t, theta t = theta0 * Real.cos (w * t) := by
  apply W2m_Pendulum_harmonic_solution <;> assumption
