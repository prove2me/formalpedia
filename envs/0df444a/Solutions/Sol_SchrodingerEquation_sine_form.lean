-- Prove2me | solution 1 for SchrodingerEquation.sine_form
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:16:45.544225+00:00
-- url     : https://prove2.me/submissions/b5fd6864-759f-48e6-a94d-46b137366910

import Definitions.Def_SchrodingerEquation_infinite_well_model

open SchrodingerEquation

namespace Ag1Aux_SchSine

/-- Uniqueness for `ψ'' = κ ψ` on `(0, L)` given matching data at an interior point. -/
theorem ode_uniq (κ : ℂ) (L : ℝ) (psi phi phi' : ℝ → ℂ)
    (hpsi1 : ∀ x ∈ Set.Ioo 0 L, HasDerivAt psi (deriv psi x) x)
    (hpsi2 : ∀ x ∈ Set.Ioo 0 L, HasDerivAt (deriv psi) (κ * psi x) x)
    (hphi1 : ∀ x, HasDerivAt phi (phi' x) x)
    (hphi2 : ∀ x, HasDerivAt phi' (κ * phi x) x)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Ioo 0 L) (h0 : psi x0 = phi x0) (h1 : deriv psi x0 = phi' x0) :
    Set.EqOn psi phi (Set.Ioo 0 L) := by
  let A : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).prod (κ • ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hA : ∀ y : ℂ × ℂ, A y = (y.2, κ * y.1) := by
    intro y; simp [A]
  have key := ODE_solution_unique_of_mem_Ioo (v := fun _ => (A : ℂ × ℂ → ℂ × ℂ))
    (s := fun _ => Set.univ) (K := ‖A‖₊)
    (f := fun x => (psi x, deriv psi x)) (g := fun x => (phi x, phi' x))
    (fun _ _ => A.lipschitz.lipschitzOnWith) hx0
    (fun t ht => ⟨by rw [hA]; exact (hpsi1 t ht).prodMk (hpsi2 t ht), Set.mem_univ _⟩)
    (fun t _ => ⟨by rw [hA]; exact (hphi1 t).prodMk (hphi2 t), Set.mem_univ _⟩)
    (by simp [h0, h1])
  intro x hx
  exact congrArg Prod.fst (key hx)

theorem eqOn_Icc (L : ℝ) (hL : 0 < L) (f g : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc 0 L))
    (hg : ContinuousOn g (Set.Icc 0 L)) (h : Set.EqOn f g (Set.Ioo 0 L)) :
    Set.EqOn f g (Set.Icc 0 L) :=
  h.of_subset_closure hf hg Set.Ioo_subset_Icc_self (by rw [closure_Ioo hL.ne])

theorem stat_ode (hbar m L E : ℝ) (psi : ℝ → ℂ) (hbar_pos : 0 < hbar) (hm : 0 < m)
    (hpsi : IsStationaryState hbar m L E psi) :
    (∀ x ∈ Set.Ioo 0 L, HasDerivAt psi (deriv psi x) x) ∧
    (∀ x ∈ Set.Ioo 0 L, HasDerivAt (deriv psi)
      ((((-(2 * m * E / hbar ^ 2)) : ℝ) : ℂ) * psi x) x) := by
  obtain ⟨-, hd1, hd2, heq, -, -⟩ := hpsi
  refine ⟨fun x hx => (hd1 x hx).hasDerivAt, fun x hx => ?_⟩
  have e := heq x hx
  have : deriv (deriv psi) x = (((-(2 * m * E / hbar ^ 2)) : ℝ) : ℂ) * psi x := by
    have hc : ((-(hbar ^ 2 / (2 * m)) : ℝ) : ℂ) ≠ 0 := by
      have : (-(hbar ^ 2 / (2 * m)) : ℝ) ≠ 0 := by
        have : 0 < hbar ^ 2 / (2 * m) := by positivity
        linarith
      exact_mod_cast this
    apply mul_left_cancel₀ hc
    rw [e]
    have h1 : (hbar : ℂ) ≠ 0 := by exact_mod_cast hbar_pos.ne'
    have h2 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp <;> ring
  rw [← this]
  exact (hd2 x hx).hasDerivAt

/-- Case `κ ≠ 0`: `ψ = A e^{rx} + B e^{-rx}` on `[0, L]`. -/
theorem exp_form (hbar m L E : ℝ) (psi : ℝ → ℂ) (hbar_pos : 0 < hbar) (hm : 0 < m)
    (hL : 0 < L) (hpsi : IsStationaryState hbar m L E psi) (r : ℂ)
    (hr : r ^ 2 = (((-(2 * m * E / hbar ^ 2)) : ℝ) : ℂ)) (hr0 : r ≠ 0) :
    ∃ A B : ℂ, ∀ x ∈ Set.Icc 0 L,
      psi x = A * Complex.exp (r * x) + B * Complex.exp ((-r) * x) := by
  obtain ⟨h1, h2⟩ := stat_ode hbar m L E psi hbar_pos hm hpsi
  set κ : ℂ := (((-(2 * m * E / hbar ^ 2)) : ℝ) : ℂ)
  set x0 : ℝ := L / 2
  have hx0 : x0 ∈ Set.Ioo 0 L := ⟨by positivity, by simp only [x0]; linarith⟩
  have hee : Complex.exp (r * x0) * Complex.exp ((-r) * x0) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have hr' : r * (deriv psi x0 / r) = deriv psi x0 := mul_div_cancel₀ _ hr0
  let A := (psi x0 + deriv psi x0 / r) / 2 * Complex.exp ((-r) * x0)
  let B := (psi x0 - deriv psi x0 / r) / 2 * Complex.exp (r * x0)
  have hd : ∀ (c : ℂ) (x : ℝ), HasDerivAt (fun x : ℝ => Complex.exp (c * x))
      (Complex.exp (c * x) * c) x := by
    intro c x
    have : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
      ((hasDerivAt_id x).ofReal_comp).const_mul c
    simpa using this.cexp
  let phi : ℝ → ℂ := fun x => A * Complex.exp (r * x) + B * Complex.exp ((-r) * x)
  let phi' : ℝ → ℂ := fun x => A * (Complex.exp (r * x) * r) + B * (Complex.exp ((-r) * x) * (-r))
  have hp1 : ∀ x, HasDerivAt phi (phi' x) x := fun x =>
    ((hd r x).const_mul A).add ((hd (-r) x).const_mul B)
  have hp2 : ∀ x, HasDerivAt phi' (κ * phi x) x := by
    intro x
    have := (((hd r x).mul_const r).const_mul A).add (((hd (-r) x).mul_const (-r)).const_mul B)
    have e : κ * phi x = A * (Complex.exp (r * x) * r * r) + B * (Complex.exp ((-r) * x) * (-r) * (-r)) := by
      simp only [phi]; rw [← hr]; ring
    rw [e]; exact this
  have hsol := ode_uniq κ L psi phi phi' h1 h2 hp1 hp2 x0 hx0
    (by simp only [phi, A, B]; linear_combination (-(psi x0)) * hee)
    (by simp only [phi', A, B]
        linear_combination (-1 : ℂ) * hr' + (-(r * (deriv psi x0 / r))) * hee)
  refine ⟨A, B, eqOn_Icc L hL psi phi hpsi.1 ?_ hsol⟩
  exact (continuous_iff_continuousAt.2 (fun x => (hp1 x).continuousAt)).continuousOn

theorem sine_core (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : 0 < E)
    (hpsi : IsStationaryState hbar m L E psi) :
    ∃ C : ℂ, ∀ x ∈ Set.Icc 0 L,
      psi x = C * (Real.sin (Real.sqrt (2 * m * E) / hbar * x) : ℂ) := by
  have hL0 : (0 : ℝ) ∈ Set.Icc 0 L := ⟨le_rfl, hL.le⟩
  set k : ℝ := Real.sqrt (2 * m * E) / hbar
  have hk2 : k ^ 2 = 2 * m * E / hbar ^ 2 := by
    simp only [k]; rw [div_pow, Real.sq_sqrt (by positivity)]
  have hkpos : 0 < k := by positivity
  obtain ⟨A, B, h⟩ := exp_form hbar m L E psi hbar_pos hm hL hpsi (Complex.I * k)
    (by rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hk2]; push_cast; ring)
    (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hkpos.ne'))
  have h0 := h 0 hL0
  rw [hpsi.2.2.2.2.1] at h0
  simp at h0
  have hB : B = -A := by linear_combination -h0
  refine ⟨2 * Complex.I * A, fun x hx => ?_⟩
  rw [h x hx, hB]
  have e1 : Complex.exp (Complex.I * k * x) = Complex.cos (k * x) + Complex.sin (k * x) * Complex.I := by
    rw [← Complex.exp_mul_I]; ring_nf
  have e2 : Complex.exp ((-(Complex.I * k)) * x) =
      Complex.cos (k * x) - Complex.sin (k * x) * Complex.I := by
    rw [show (-(Complex.I * k)) * (x : ℂ) = (-(k * x : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]; ring
  rw [e1, e2]
  push_cast
  ring_nf

end Ag1Aux_SchSine

open Ag1Aux_SchSine

theorem solution (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : 0 < E)
    (hpsi : IsStationaryState hbar m L E psi) :
    ∃ C : ℂ, ∀ x ∈ Set.Icc 0 L,
      psi x = C * (Real.sin (Real.sqrt (2 * m * E) / hbar * x) : ℂ) :=
  sine_core hbar m L E psi hbar_pos hm hL hE hpsi
