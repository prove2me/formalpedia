-- Prove2me | solution 1 for SchrodingerEquation.energy_quantization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:17:10.960613+00:00
-- url     : https://prove2.me/submissions/1a14c010-c057-40bb-9773-593b951b8717

import Definitions.Def_SchrodingerEquation_infinite_well_model

open SchrodingerEquation

namespace Ag1Aux_SchEnergy

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

/-- Case `κ = 0`: `ψ = A + B x` on `[0, L]`. -/
theorem lin_form (hbar m L : ℝ) (psi : ℝ → ℂ) (hbar_pos : 0 < hbar) (hm : 0 < m)
    (hL : 0 < L) (hpsi : IsStationaryState hbar m L 0 psi) :
    ∃ A B : ℂ, ∀ x ∈ Set.Icc 0 L, psi x = A + B * x := by
  obtain ⟨h1, h2⟩ := stat_ode hbar m L 0 psi hbar_pos hm hpsi
  set x0 : ℝ := L / 2
  have hx0 : x0 ∈ Set.Ioo 0 L := ⟨by positivity, by simp only [x0]; linarith⟩
  let phi : ℝ → ℂ := fun x => (psi x0 - deriv psi x0 * x0) + deriv psi x0 * x
  let phi' : ℝ → ℂ := fun _ => deriv psi x0
  have hp1 : ∀ x, HasDerivAt phi (phi' x) x := by
    intro x
    exact ((((hasDerivAt_id x).ofReal_comp).const_mul (deriv psi x0)).const_add
      (psi x0 - deriv psi x0 * x0)).congr_deriv (by simp [phi'])
  have hp2 : ∀ x, HasDerivAt phi' ((((-(2 * m * 0 / hbar ^ 2)) : ℝ) : ℂ) * phi x) x := by
    intro x; simpa [phi'] using hasDerivAt_const x (deriv psi x0)
  have hsol := ode_uniq _ L psi phi phi' h1 h2 hp1 hp2 x0 hx0 (by simp [phi]) (by simp [phi'])
  refine ⟨psi x0 - deriv psi x0 * x0, deriv psi x0, eqOn_Icc L hL psi phi hpsi.1 ?_ hsol⟩
  exact (continuous_iff_continuousAt.2 (fun x => (hp1 x).continuousAt)).continuousOn

theorem trivial_core (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : E ≤ 0)
    (hpsi : IsStationaryState hbar m L E psi) :
    ∀ x ∈ Set.Icc 0 L, psi x = 0 := by
  have hL0 : (0 : ℝ) ∈ Set.Icc 0 L := ⟨le_rfl, hL.le⟩
  have hLL : L ∈ Set.Icc 0 L := ⟨hL.le, le_rfl⟩
  rcases hE.lt_or_eq with hE | hE
  · set k : ℝ := Real.sqrt (2 * m * E / hbar ^ 2 * (-1))
    have hk2 : k ^ 2 = -(2 * m * E / hbar ^ 2) := by
      rw [Real.sq_sqrt]; · ring
      have : 2 * m * E / hbar ^ 2 < 0 := div_neg_of_neg_of_pos (by nlinarith) (by positivity)
      linarith
    have hkpos : 0 < k := Real.sqrt_pos.2 (by
      have : 2 * m * E / hbar ^ 2 < 0 := div_neg_of_neg_of_pos (by nlinarith) (by positivity)
      linarith)
    obtain ⟨A, B, h⟩ := exp_form hbar m L E psi hbar_pos hm hL hpsi (k : ℂ)
      (by rw [← hk2]; push_cast; ring) (by exact_mod_cast hkpos.ne')
    have h0 := h 0 hL0
    rw [hpsi.2.2.2.2.1] at h0
    simp at h0
    have hB : B = -A := by linear_combination -h0
    have hLv := h L hLL
    rw [hpsi.2.2.2.2.2, hB] at hLv
    have hne : Complex.exp ((k : ℂ) * L) - Complex.exp ((-(k : ℂ)) * L) ≠ 0 := by
      have e1 : Complex.exp ((k : ℂ) * L) = ((Real.exp (k * L) : ℝ) : ℂ) := by
        push_cast; ring_nf
      have e2 : Complex.exp ((-(k : ℂ)) * L) = ((Real.exp (-k * L) : ℝ) : ℂ) := by
        push_cast; ring_nf
      rw [e1, e2, ← Complex.ofReal_sub]
      have : Real.exp (-k * L) < Real.exp (k * L) := Real.exp_lt_exp.2 (by nlinarith)
      exact_mod_cast (sub_pos.2 this).ne'
    have hA : A = 0 := by
      have : A * (Complex.exp ((k : ℂ) * L) - Complex.exp ((-(k : ℂ)) * L)) = 0 := by
        linear_combination -hLv
      exact (mul_eq_zero.1 this).resolve_right hne
    intro x hx
    rw [h x hx, hB, hA]; simp
  · subst hE
    obtain ⟨A, B, h⟩ := lin_form hbar m L psi hbar_pos hm hL hpsi
    have h0 := h 0 hL0
    rw [hpsi.2.2.2.2.1] at h0
    simp at h0
    have hLv := h L hLL
    rw [hpsi.2.2.2.2.2, ← h0, zero_add] at hLv
    have hB : B = 0 := by
      rcases mul_eq_zero.1 hLv.symm with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hL.ne'
    intro x hx
    rw [h x hx, ← h0, hB]; simp

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

end Ag1Aux_SchEnergy

open Ag1Aux_SchEnergy

theorem solution (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L)
    (hpsi : IsStationaryState hbar m L E psi)
    (hne : ∃ x ∈ Set.Ioo 0 L, psi x ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ E = energyLevel hbar m L n := by
  obtain ⟨x1, hx1, hpx⟩ := hne
  rcases le_or_gt E 0 with hE | hE
  · exact absurd (trivial_core hbar m L E psi hbar_pos hm hL hE hpsi x1
      (Set.Ioo_subset_Icc_self hx1)) hpx
  obtain ⟨C, hC⟩ := sine_core hbar m L E psi hbar_pos hm hL hE hpsi
  set k : ℝ := Real.sqrt (2 * m * E) / hbar
  have hk2 : k ^ 2 = 2 * m * E / hbar ^ 2 := by
    simp only [k]; rw [div_pow, Real.sq_sqrt (by positivity)]
  have hkpos : 0 < k := by positivity
  have hC0 : C ≠ 0 := by
    rintro rfl
    exact hpx (by rw [hC x1 (Set.Ioo_subset_Icc_self hx1)]; simp)
  have hLv := hC L ⟨hL.le, le_rfl⟩
  rw [hpsi.2.2.2.2.2] at hLv
  have hs : Real.sin (k * L) = 0 := by
    rcases mul_eq_zero.1 hLv.symm with h | h
    · exact absurd h hC0
    · exact_mod_cast h
  -- quantization of the wavenumber
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
  have hpos : 0 < (n : ℝ) * Real.pi := by rw [hn]; positivity
  have hn0 : 0 < n := by
    by_contra hc
    push Not at hc
    have : (n : ℝ) ≤ 0 := by exact_mod_cast hc
    nlinarith [Real.pi_pos]
  refine ⟨n.toNat, by omega, ?_⟩
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have : ((n.toNat : ℤ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0.le
    rw [← this]; norm_cast
  rw [energyLevel, hcast]
  have h2 : (n : ℝ) ^ 2 * Real.pi ^ 2 = (k * L) ^ 2 := by rw [← hn]; ring
  have hE' : E = k ^ 2 * hbar ^ 2 / (2 * m) := by
    rw [hk2]; field_simp
  rw [h2]
  nth_rewrite 1 [hE']
  field_simp
