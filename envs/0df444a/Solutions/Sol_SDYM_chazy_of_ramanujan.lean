-- Prove2me | solution 1 for SDYM.chazy_of_ramanujan
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:06:54.899792+00:00
-- url     : https://prove2.me/submissions/5768b0cf-e75d-4db5-8e54-17d16b178f6c

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

open SDYM
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem W3b_SDYM_sq {f : ℂ → ℂ} {f' t : ℂ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun x => f x ^ 2) (2 * f t * f') t := by
  have e : (fun x => f x ^ 2) = fun x => f x * f x := funext fun x => sq (f x)
  rw [e]
  exact (h.mul h).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)

theorem W3b_SDYM_cube {f : ℂ → ℂ} {f' t : ℂ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun x => f x ^ 3) (3 * f t ^ 2 * f') t := by
  have e : (fun x => f x ^ 3) = fun x => f x * f x * f x := funext fun x => by ring
  rw [e]
  exact ((h.mul h).mul h).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)

theorem W3b_SDYM_powk {f : ℂ → ℂ} {f' t : ℂ} (k : ℕ) (h : HasDerivAt f f' t) :
    HasDerivAt (fun x => f x ^ (k + 1)) ((k + 1) * f t ^ k * f') t := by
  induction k with
  | zero =>
    have e : (fun x => f x ^ (0 + 1)) = f := funext fun x => by ring
    rw [e]
    exact h.congr_deriv (by push_cast; ring)
  | succ k ih =>
    have e : (fun x => f x ^ (k + 1 + 1)) = fun x => f x ^ (k + 1) * f x :=
      funext fun x => by ring
    rw [e]
    exact (ih.mul h).congr_deriv (by push_cast; ring)

theorem W3b_SDYM_scaled (k : ℂ) (p q r : ℂ → ℂ) (t : ℂ)
    (hp : HasDerivAt p (k * Complex.I * (p t ^ 2 - q t) / 6) t)
    (hq : HasDerivAt q (2 * k * Complex.I * (p t * q t - r t) / 3) t)
    (hr : HasDerivAt r (k * Complex.I * (p t * r t - q t ^ 2)) t) :
    HasDerivAt (fun t => Complex.I * k * p t) (-(k ^ 2 * (p t ^ 2 - q t) / 6)) t ∧
    HasDerivAt (fun t => -(k ^ 2 * (p t ^ 2 - q t) / 6))
      (-(Complex.I * k ^ 3 * (p t ^ 3 - 3 * p t * q t + 2 * r t) / 18)) t ∧
    HasDerivAt (fun t => -(Complex.I * k ^ 3 * (p t ^ 3 - 3 * p t * q t + 2 * r t) / 18))
      (2 * (Complex.I * k * p t) *
          (-(Complex.I * k ^ 3 * (p t ^ 3 - 3 * p t * q t + 2 * r t) / 18))
        - 3 * (-(k ^ 2 * (p t ^ 2 - q t) / 6)) ^ 2) t := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hp.const_mul (Complex.I * k)).congr_deriv
      (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring_nf <;> (try simp only [Complex.I_sq]) <;> ring)
  · exact ((((W3b_SDYM_sq hp).sub hq).const_mul (k ^ 2)).div_const 6).neg.congr_deriv
      (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring_nf <;> (try simp only [Complex.I_sq]) <;> ring)
  · exact (((((W3b_SDYM_cube hp).sub ((hp.const_mul 3).mul hq)).add
      (hr.const_mul 2)).const_mul (Complex.I * k ^ 3)).div_const 18).neg.congr_deriv
      (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring_nf <;> (try simp only [Complex.I_sq]) <;> ring)

theorem W3b_SDYM_chazy_of_ramanujan_tau
    (s : Set ℂ) (P Q R : ℂ → ℂ) (h : IsRamanujanTauSolution s P Q R) :
    IsChazySolution s
      (fun z => Complex.I * P z)
      (fun z => -((P z ^ 2 - Q z) / 6))
      (fun z => -(Complex.I * (P z ^ 3 - 3 * P z * Q z + 2 * R z) / 18)) := by
  obtain ⟨hP, hQ, hR⟩ := h
  have key := fun t (ht : t ∈ s) => W3b_SDYM_scaled 1 P Q R t
    ((hP t ht).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)) ((hQ t ht).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring))
    ((hR t ht).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring))
  simp only [IsChazySolution]
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · convert (key t ht).1 using 1 <;> first | rfl | (funext x; ring) | ring
  · convert (key t ht).2.1 using 1 <;> first | rfl | (funext x; ring) | ring
  · convert (key t ht).2.2 using 1 <;> first | rfl | (funext x; ring) | ring

theorem W3b_SDYM_ramanujan_tau_of_ramanujan_q
    (U : Set ℂ) (P Q R Pd Qd Rd : ℂ → ℂ)
    (h : IsRamanujanQSolution U P Q R Pd Qd Rd) :
    IsRamanujanTauSolution {z : ℂ | Complex.exp (2 * Complex.I * z) ∈ U}
      (fun z => P (Complex.exp (2 * Complex.I * z)))
      (fun z => Q (Complex.exp (2 * Complex.I * z)))
      (fun z => R (Complex.exp (2 * Complex.I * z))) := by
  obtain ⟨hP, hQ, hR, hPd, hQd, hRd⟩ := h
  have he : ∀ z : ℂ, HasDerivAt (fun z => Complex.exp (2 * Complex.I * z))
      (Complex.exp (2 * Complex.I * z) * (2 * Complex.I)) z := fun z =>
    (((hasDerivAt_id' z).const_mul (2 * Complex.I)).cexp).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
  simp only [IsRamanujanTauSolution]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have hc : HasDerivAt (fun z => P (Complex.exp (2 * Complex.I * z)))
        (Pd (Complex.exp (2 * Complex.I * z)) *
          (Complex.exp (2 * Complex.I * z) * (2 * Complex.I))) z :=
      (hP (Complex.exp (2 * Complex.I * z)) hz).comp z (he z)
    exact hc.congr_deriv
      (by linear_combination (2 * Complex.I) * hPd (Complex.exp (2 * Complex.I * z)) hz)
  · have hc : HasDerivAt (fun z => Q (Complex.exp (2 * Complex.I * z)))
        (Qd (Complex.exp (2 * Complex.I * z)) *
          (Complex.exp (2 * Complex.I * z) * (2 * Complex.I))) z :=
      (hQ (Complex.exp (2 * Complex.I * z)) hz).comp z (he z)
    exact hc.congr_deriv
      (by linear_combination (2 * Complex.I) * hQd (Complex.exp (2 * Complex.I * z)) hz)
  · have hc : HasDerivAt (fun z => R (Complex.exp (2 * Complex.I * z)))
        (Rd (Complex.exp (2 * Complex.I * z)) *
          (Complex.exp (2 * Complex.I * z) * (2 * Complex.I))) z :=
      (hR (Complex.exp (2 * Complex.I * z)) hz).comp z (he z)
    exact hc.congr_deriv
      (by linear_combination (2 * Complex.I) * hRd (Complex.exp (2 * Complex.I * z)) hz)

theorem solution
    (U : Set ℂ) (P Q R Pd Qd Rd : ℂ → ℂ)
    (h : IsRamanujanQSolution U P Q R Pd Qd Rd) :
    IsChazySolution {t : ℂ | Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t) ∈ U}
      (fun t => Complex.I * (Real.pi : ℂ) *
        P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t)))
      (fun t => -((Real.pi : ℂ) ^ 2 *
        (P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t)) ^ 2
          - Q (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t))) / 6))
      (fun t => -(Complex.I * (Real.pi : ℂ) ^ 3 *
        (P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t)) ^ 3
          - 3 * P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t))
              * Q (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t))
          + 2 * R (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t))) / 18)) := by
  obtain ⟨hP, hQ, hR, hPd, hQd, hRd⟩ := h
  have he : ∀ z : ℂ, HasDerivAt (fun z => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) * (2 * (Real.pi : ℂ) * Complex.I)) z :=
    fun z => (((hasDerivAt_id' z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp).congr_deriv
      (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
  have key := fun t (ht : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t) ∈ U) =>
    W3b_SDYM_scaled (Real.pi : ℂ)
      (fun z => P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)))
      (fun z => Q (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)))
      (fun z => R (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) t
      (((hP _ ht).comp t (he t)).congr_deriv
        (by linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hPd _ ht))
      (((hQ _ ht).comp t (he t)).congr_deriv
        (by linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hQd _ ht))
      (((hR _ ht).comp t (he t)).congr_deriv
        (by linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hRd _ ht))
  simp only [IsChazySolution]
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · convert (key t ht).1 using 1 <;> first | rfl | (funext x; ring) | ring
  · convert (key t ht).2.1 using 1 <;> first | rfl | (funext x; ring) | ring
  · convert (key t ht).2.2 using 1 <;> first | rfl | (funext x; ring) | ring

theorem W3b_SDYM_chazy_of_classical_darboux_halphen
    (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ) (h : IsClassicalDHSolution s w₁ w₂ w₃) :
    IsChazySolution s
      (fun t => -2 * (w₁ t + w₂ t + w₃ t))
      (fun t => 2 * (w₁ t * w₂ t + w₂ t * w₃ t + w₃ t * w₁ t))
      (fun t => -12 * (w₁ t * w₂ t * w₃ t)) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [IsChazySolution]
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact ((((h1 t ht).add (h2 t ht)).add (h3 t ht)).const_mul (-2)).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
  · exact (((((h1 t ht).mul (h2 t ht)).add ((h2 t ht).mul (h3 t ht))).add
      ((h3 t ht).mul (h1 t ht))).const_mul 2).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
  · exact ((((h1 t ht).mul (h2 t ht)).mul (h3 t ht)).const_mul (-12)).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)

theorem W3b_SDYM_generalized_chazy_of_darboux_halphen
    (n : ℂ) (hn : n ≠ 0) (hn36 : n ^ 2 ≠ 36) (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ)
    (h₁ : ∀ t ∈ s, HasDerivAt w₁ (w₂ t * w₃ t - w₁ t * (w₂ t + w₃ t)
      + (2 / n) ^ 2 * ((w₁ t - w₂ t) * (w₃ t - w₁ t) + (w₂ t - w₃ t) * (w₁ t - w₂ t)
        + (w₃ t - w₁ t) * (w₂ t - w₃ t))) t)
    (h₂ : ∀ t ∈ s, HasDerivAt w₂ (w₃ t * w₁ t - w₂ t * (w₃ t + w₁ t)
      + (2 / n) ^ 2 * ((w₁ t - w₂ t) * (w₃ t - w₁ t) + (w₂ t - w₃ t) * (w₁ t - w₂ t)
        + (w₃ t - w₁ t) * (w₂ t - w₃ t))) t)
    (h₃ : ∀ t ∈ s, HasDerivAt w₃ (w₁ t * w₂ t - w₃ t * (w₁ t + w₂ t)
      + (2 / n) ^ 2 * ((w₁ t - w₂ t) * (w₃ t - w₁ t) + (w₂ t - w₃ t) * (w₁ t - w₂ t)
        + (w₃ t - w₁ t) * (w₂ t - w₃ t))) t) :
    IsGeneralizedChazySolution n s
      (fun t => -2 * (w₁ t + w₂ t + w₃ t))
      (fun t => 2 * (w₁ t * w₂ t + w₂ t * w₃ t + w₃ t * w₁ t)
        - 6 * (4 / n ^ 2 * (3 * (w₁ t * w₂ t + w₂ t * w₃ t + w₃ t * w₁ t)
          - (w₁ t + w₂ t + w₃ t) ^ 2)))
      (fun t => -12 * (w₁ t * w₂ t * w₃ t)
        + 4 / n ^ 2 * (-4 * (w₁ t + w₂ t + w₃ t) ^ 3
          + 108 * (w₁ t * w₂ t * w₃ t))) := by
  have h36 : (36 : ℂ) - n ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hn36)
  simp only [IsGeneralizedChazySolution]
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact ((((h₁ t ht).add (h₂ t ht)).add (h₃ t ht)).const_mul (-2)).congr_deriv
      (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); field_simp; ring)
  · have hS := ((h₁ t ht).add (h₂ t ht)).add (h₃ t ht)
    have hP2 := (((h₁ t ht).mul (h₂ t ht)).add ((h₂ t ht).mul (h₃ t ht))).add
      ((h₃ t ht).mul (h₁ t ht))
    exact ((hP2.const_mul 2).sub ((((hP2.const_mul 3).sub (W3b_SDYM_sq hS)).const_mul
      (4 / n ^ 2)).const_mul 6)).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); field_simp; ring)
  · have hS := ((h₁ t ht).add (h₂ t ht)).add (h₃ t ht)
    have hP2 := (((h₁ t ht).mul (h₂ t ht)).add ((h₂ t ht).mul (h₃ t ht))).add
      ((h₃ t ht).mul (h₁ t ht))
    have hP3 := ((h₁ t ht).mul (h₂ t ht)).mul (h₃ t ht)
    exact ((hP3.const_mul (-12)).add ((((W3b_SDYM_cube hS).const_mul (-4)).add
      (hP3.const_mul 108)).const_mul (4 / n ^ 2))).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); field_simp; ring)

theorem W3b_SDYM_darboux_halphen_first_integrals
    (s : Set ℂ) (w₁ w₂ w₃ x₁ x₂ x₃ : ℂ → ℂ)
    (h : IsGeneralizedDHSolution s w₁ w₂ w₃ x₁ x₂ x₃)
    (hdist : ∀ t ∈ s, w₁ t ≠ w₂ t ∧ w₂ t ≠ w₃ t ∧ w₃ t ≠ w₁ t) :
    (∀ t ∈ s, HasDerivAt
        (fun z => x₁ z ^ 2 / ((w₁ z - w₂ z) * (w₃ z - w₁ z))) 0 t) ∧
    (∀ t ∈ s, HasDerivAt
        (fun z => x₂ z ^ 2 / ((w₂ z - w₃ z) * (w₁ z - w₂ z))) 0 t) ∧
    (∀ t ∈ s, HasDerivAt
        (fun z => x₃ z ^ 2 / ((w₃ z - w₁ z) * (w₂ z - w₃ z))) 0 t) := by
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨d12, d23, d31⟩ := hdist t ht
    have hden : (w₁ t - w₂ t) * (w₃ t - w₁ t) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr d12) (sub_ne_zero.mpr d31)
    have e : (fun z => x₁ z ^ 2 / ((w₁ z - w₂ z) * (w₃ z - w₁ z)))
        = fun z => x₁ z * x₁ z / ((w₁ z - w₂ z) * (w₃ z - w₁ z)) :=
      funext fun z => by ring
    rw [e]
    exact (((g1 t ht).mul (g1 t ht)).div (((h1 t ht).sub (h2 t ht)).mul
      ((h3 t ht).sub (h1 t ht))) hden).congr_deriv
      (div_eq_zero_iff.mpr (Or.inl (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)))
  · obtain ⟨d12, d23, d31⟩ := hdist t ht
    have hden : (w₂ t - w₃ t) * (w₁ t - w₂ t) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr d23) (sub_ne_zero.mpr d12)
    have e : (fun z => x₂ z ^ 2 / ((w₂ z - w₃ z) * (w₁ z - w₂ z)))
        = fun z => x₂ z * x₂ z / ((w₂ z - w₃ z) * (w₁ z - w₂ z)) :=
      funext fun z => by ring
    rw [e]
    exact (((g2 t ht).mul (g2 t ht)).div (((h2 t ht).sub (h3 t ht)).mul
      ((h1 t ht).sub (h2 t ht))) hden).congr_deriv
      (div_eq_zero_iff.mpr (Or.inl (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)))
  · obtain ⟨d12, d23, d31⟩ := hdist t ht
    have hden : (w₃ t - w₁ t) * (w₂ t - w₃ t) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr d31) (sub_ne_zero.mpr d23)
    have e : (fun z => x₃ z ^ 2 / ((w₃ z - w₁ z) * (w₂ z - w₃ z)))
        = fun z => x₃ z * x₃ z / ((w₃ z - w₁ z) * (w₂ z - w₃ z)) :=
      funext fun z => by ring
    rw [e]
    exact (((g3 t ht).mul (g3 t ht)).div (((h3 t ht).sub (h1 t ht)).mul
      ((h2 t ht).sub (h3 t ht))) hden).congr_deriv
      (div_eq_zero_iff.mpr (Or.inl (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)))

theorem W3b_SDYM_chazy_mobius_invariance
    (s : Set ℂ) (y y₁ y₂ : ℂ → ℂ) (h : IsChazySolution s y y₁ y₂)
    (a b c d : ℂ) (hdet : a * d - b * c = 1) :
    IsChazySolution {t : ℂ | c * t + d ≠ 0 ∧ (a * t + b) / (c * t + d) ∈ s}
      (fun t => y ((a * t + b) / (c * t + d)) / (c * t + d) ^ 2 - 6 * c / (c * t + d))
      (fun t => -2 * c * y ((a * t + b) / (c * t + d)) / (c * t + d) ^ 3
        + y₁ ((a * t + b) / (c * t + d)) / (c * t + d) ^ 4
        + 6 * c ^ 2 / (c * t + d) ^ 2)
      (fun t => 6 * c ^ 2 * y ((a * t + b) / (c * t + d)) / (c * t + d) ^ 4
        - 6 * c * y₁ ((a * t + b) / (c * t + d)) / (c * t + d) ^ 5
        + y₂ ((a * t + b) / (c * t + d)) / (c * t + d) ^ 6
        - 12 * c ^ 3 / (c * t + d) ^ 3) := by
  obtain ⟨g0, g1, g2⟩ := h
  have hu : ∀ t, c * t + d ≠ 0 →
      HasDerivAt (fun t => (a * t + b) / (c * t + d)) (1 / (c * t + d) ^ 2) t := by
    intro t ht
    have := (((hasDerivAt_id' t).const_mul a).add_const b).div
      (((hasDerivAt_id' t).const_mul c).add_const d) ht
    refine this.congr_deriv ?_
    rw [div_left_inj' (pow_ne_zero 2 ht)]
    linear_combination hdet
  simp only [IsChazySolution]
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨he, hs⟩ := ht
    have hE : HasDerivAt (fun t => c * t + d) c t :=
      (((hasDerivAt_id' t).const_mul c).add_const d).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
    have hE2 := W3b_SDYM_sq hE
    have hE3 := W3b_SDYM_powk 2 hE
    have hE4 := W3b_SDYM_powk 3 hE
    have hE5 := W3b_SDYM_powk 4 hE
    have hE6 := W3b_SDYM_powk 5 hE
    have hyu : HasDerivAt (fun t => y ((a * t + b) / (c * t + d)))
        (y₁ ((a * t + b) / (c * t + d)) * (1 / (c * t + d) ^ 2)) t :=
      (g0 _ hs).comp t (hu t he)
    have hy1u : HasDerivAt (fun t => y₁ ((a * t + b) / (c * t + d)))
        (y₂ ((a * t + b) / (c * t + d)) * (1 / (c * t + d) ^ 2)) t :=
      (g1 _ hs).comp t (hu t he)
    have hy2u : HasDerivAt (fun t => y₂ ((a * t + b) / (c * t + d)))
        ((2 * y ((a * t + b) / (c * t + d)) * y₂ ((a * t + b) / (c * t + d))
          - 3 * y₁ ((a * t + b) / (c * t + d)) ^ 2) * (1 / (c * t + d) ^ 2)) t :=
      (g2 _ hs).comp t (hu t he)
    exact ((hyu.div hE2 (pow_ne_zero 2 he)).sub
        ((hasDerivAt_const t (6 * c)).div hE he)).congr_deriv
        (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); push_cast; field_simp; ring)
  · obtain ⟨he, hs⟩ := ht
    have hE : HasDerivAt (fun t => c * t + d) c t :=
      (((hasDerivAt_id' t).const_mul c).add_const d).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
    have hE2 := W3b_SDYM_sq hE
    have hE3 := W3b_SDYM_powk 2 hE
    have hE4 := W3b_SDYM_powk 3 hE
    have hE5 := W3b_SDYM_powk 4 hE
    have hE6 := W3b_SDYM_powk 5 hE
    have hyu : HasDerivAt (fun t => y ((a * t + b) / (c * t + d)))
        (y₁ ((a * t + b) / (c * t + d)) * (1 / (c * t + d) ^ 2)) t :=
      (g0 _ hs).comp t (hu t he)
    have hy1u : HasDerivAt (fun t => y₁ ((a * t + b) / (c * t + d)))
        (y₂ ((a * t + b) / (c * t + d)) * (1 / (c * t + d) ^ 2)) t :=
      (g1 _ hs).comp t (hu t he)
    have hy2u : HasDerivAt (fun t => y₂ ((a * t + b) / (c * t + d)))
        ((2 * y ((a * t + b) / (c * t + d)) * y₂ ((a * t + b) / (c * t + d))
          - 3 * y₁ ((a * t + b) / (c * t + d)) ^ 2) * (1 / (c * t + d) ^ 2)) t :=
      (g2 _ hs).comp t (hu t he)
    exact ((((hyu.const_mul (-2 * c)).div hE3 (pow_ne_zero 3 he)).add
        (hy1u.div hE4 (pow_ne_zero 4 he))).add
        ((hasDerivAt_const t (6 * c ^ 2)).div hE2 (pow_ne_zero 2 he))).congr_deriv
        (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); push_cast; field_simp; ring)
  · obtain ⟨he, hs⟩ := ht
    have hE : HasDerivAt (fun t => c * t + d) c t :=
      (((hasDerivAt_id' t).const_mul c).add_const d).congr_deriv (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); ring)
    have hE2 := W3b_SDYM_sq hE
    have hE3 := W3b_SDYM_powk 2 hE
    have hE4 := W3b_SDYM_powk 3 hE
    have hE5 := W3b_SDYM_powk 4 hE
    have hE6 := W3b_SDYM_powk 5 hE
    have hyu : HasDerivAt (fun t => y ((a * t + b) / (c * t + d)))
        (y₁ ((a * t + b) / (c * t + d)) * (1 / (c * t + d) ^ 2)) t :=
      (g0 _ hs).comp t (hu t he)
    have hy1u : HasDerivAt (fun t => y₁ ((a * t + b) / (c * t + d)))
        (y₂ ((a * t + b) / (c * t + d)) * (1 / (c * t + d) ^ 2)) t :=
      (g1 _ hs).comp t (hu t he)
    have hy2u : HasDerivAt (fun t => y₂ ((a * t + b) / (c * t + d)))
        ((2 * y ((a * t + b) / (c * t + d)) * y₂ ((a * t + b) / (c * t + d))
          - 3 * y₁ ((a * t + b) / (c * t + d)) ^ 2) * (1 / (c * t + d) ^ 2)) t :=
      (g2 _ hs).comp t (hu t he)
    exact (((((hyu.const_mul (6 * c ^ 2)).div hE4 (pow_ne_zero 4 he)).sub
        ((hy1u.const_mul (6 * c)).div hE5 (pow_ne_zero 5 he))).add
        (hy2u.div hE6 (pow_ne_zero 6 he))).sub
        ((hasDerivAt_const t (12 * c ^ 3)).div hE3 (pow_ne_zero 3 he))).congr_deriv
        (by (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]); push_cast; field_simp; ring)

theorem W3b_SDYM_rhs_diag (a b c : ℂ) :
    (Matrix.diagonal ![a, b, c]).adjugate.transpose
      + (Matrix.diagonal ![a, b, c]).transpose * Matrix.diagonal ![a, b, c]
      - Matrix.trace (Matrix.diagonal ![a, b, c]) • Matrix.diagonal ![a, b, c]
      = Matrix.diagonal ![b * c - a * (b + c), c * a - b * (c + a), a * b - c * (a + b)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.diagonal] <;> ring

theorem W3b_SDYM_matrix_flow_diagonal_iff_classical_darboux_halphen
    (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ) (M : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (hM : ∀ t : ℂ, M t = Matrix.diagonal ![w₁ t, w₂ t, w₃ t]) :
    ((∀ t ∈ s, ∀ i j, HasDerivAt (fun z => M z i j)
        (((M t).adjugate.transpose + (M t).transpose * M t
          - Matrix.trace (M t) • M t) i j) t)
      ↔ IsClassicalDHSolution s w₁ w₂ w₃) := by
  have hM' : M = fun t => Matrix.diagonal ![w₁ t, w₂ t, w₃ t] := funext hM
  subst hM'
  simp only [W3b_SDYM_rhs_diag]
  constructor
  · intro H
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simpa using H t ht 0 0
    · simpa using H t ht 1 1
    · simpa using H t ht 2 2
  · rintro ⟨h1, h2, h3⟩ t ht i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first
      | exact hasDerivAt_const _ _
      | exact h1 t ht
      | exact h2 t ht
      | exact h3 t ht
