-- Prove2me | solution 1 for RotationLadder.Protocol.euler_xzx
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:38:04.122095+00:00
-- url     : https://prove2.me/submissions/cf03dcd9-b69a-4f4f-8ea8-b787eac67377

import Mathlib
import Definitions.Def_RotationLadder_Protocol_xRot

namespace Aux_RLexzx

open RotationLadder.Protocol Complex

noncomputable def E (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

theorem E_add (s t : ℝ) : E (s + t) = E s * E t := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem polar (z : ℂ) : z = (‖z‖ : ℂ) * E (Complex.arg z) := by
  unfold E
  rw [mul_comm Complex.I]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

theorem E_zero : E 0 = 1 := by simp [E]

theorem E_pi : E Real.pi = -1 := by
  unfold E; rw [mul_comm]; exact Complex.exp_pi_mul_I

theorem E_pi_div_two : E (Real.pi / 2) = Complex.I := by
  unfold E
  rw [mul_comm]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

theorem P_eq (θ : ℝ) : (1 + E (2 * θ)) / 2 = E θ * (Real.cos θ : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  unfold E
  rw [mul_div_assoc', mul_add, ← Complex.exp_add, ← Complex.exp_add,
    show Complex.I * (θ : ℂ) + -(θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero,
    show Complex.I * (θ : ℂ) + (θ : ℂ) * Complex.I = Complex.I * ((2 * θ : ℝ) : ℂ) by
      push_cast; ring]
  ring

theorem Q_eq (θ : ℝ) : (1 - E (2 * θ)) / 2 = -Complex.I * E θ * (Real.sin θ : ℂ) := by
  rw [Complex.ofReal_sin, Complex.sin]
  unfold E
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show Complex.I * (θ : ℂ) + -(θ : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero]
  have h2 : Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2 +
    (Complex.exp (Complex.I * (θ : ℂ)) * (Complex.exp (-(θ : ℂ) * Complex.I) -
      Complex.exp ((θ : ℂ) * Complex.I)) / 2) * hI

theorem star_E (t : ℝ) : star (E t) = E (-t) := by
  unfold E
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]

theorem star_polar (z : ℂ) : star z = (‖z‖ : ℂ) * E (-Complex.arg z) := by
  conv_lhs => rw [polar z]
  rw [star_mul', star_E]
  simp [Complex.conj_ofReal]

theorem xRot_apply (β : ℝ) (i j : Bool) :
    xRot β i j = if i = j then (1 + E β) / 2 else (1 - E β) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  cases i <;> cases j <;>
    simp [xRot, zRot, QAlgorithms.hadamard, Matrix.mul_apply, Fintype.sum_bool, E] <;>
    field_simp <;> ring_nf <;> simp [h2] <;> ring

theorem ZXZ_apply (κ α β γ : ℝ) (i j : Bool) :
    (Complex.exp (Complex.I * (κ : ℂ)) • (zRot α * xRot β * zRot γ)) i j =
      E κ * (if i then E α else 1) * xRot β i j * (if j then E γ else 1) := by
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold zRot
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold E
  ring

theorem zxz (V : Matrix Bool Bool ℂ) (hV : V ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ κ α β γ : ℝ, V = Complex.exp (Complex.I * (κ : ℂ)) • (zRot α * xRot β * zRot γ) := by
  have h1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have h2 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have e1 := congrFun (congrFun h1 false) false
  have e2 := congrFun (congrFun h1 false) true
  have e3 := congrFun (congrFun h1 true) true
  have e4 := congrFun (congrFun h2 false) false
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show false ≠ true by decide)] at e1 e2 e3 e4
  set a := V false false with ha
  set b := V false true with hb
  set c := V true false with hc
  set d := V true true with hd
  have nsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  have nsq' : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [mul_comm]; exact nsq z
  rw [nsq, nsq] at e1 e3
  rw [nsq', nsq'] at e4
  have n1 : ‖a‖ ^ 2 + ‖c‖ ^ 2 = 1 := by
    have h : ‖c‖ ^ 2 + ‖a‖ ^ 2 = 1 := by exact_mod_cast e1
    linarith
  have n3 : ‖b‖ ^ 2 + ‖d‖ ^ 2 = 1 := by
    have h : ‖d‖ ^ 2 + ‖b‖ ^ 2 = 1 := by exact_mod_cast e3
    linarith
  have n4 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    have h : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by exact_mod_cast e4
    linarith
  by_cases hc0 : c = 0
  · have hcn : ‖c‖ = 0 := by rw [hc0, norm_zero]
    have hb0 : b = 0 := by
      have : ‖b‖ ^ 2 = 0 := by nlinarith
      exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
    have hbn : ‖b‖ = 0 := by rw [hb0, norm_zero]
    have na : ‖a‖ = 1 := by
      have : ‖a‖ ^ 2 = 1 := by nlinarith
      nlinarith [norm_nonneg a]
    have nd : ‖d‖ = 1 := by
      have : ‖d‖ ^ 2 = 1 := by nlinarith
      nlinarith [norm_nonneg d]
    refine ⟨Complex.arg a, Complex.arg d - Complex.arg a, 0, 0, ?_⟩
    ext i j
    rw [ZXZ_apply, xRot_apply, E_zero]
    cases i <;> cases j
    · simp only [if_true, ite_false, Bool.false_eq_true]
      rw [← ha]
      conv_lhs => rw [polar a, na]
      norm_num
    · simp only [ite_true, ite_false, Bool.false_eq_true]
      rw [← hb, hb0]; ring
    · simp only [ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
      rw [← hc, hc0]; ring
    · simp only [ite_true]
      rw [← hd]
      conv_lhs => rw [polar d, nd]
      rw [← E_add, show Complex.arg a + (Complex.arg d - Complex.arg a) = Complex.arg d by ring]
      norm_num
  · by_cases ha0 : a = 0
    · have han : ‖a‖ = 0 := by rw [ha0, norm_zero]
      have nc : ‖c‖ = 1 := by
        have : ‖c‖ ^ 2 = 1 := by nlinarith
        nlinarith [norm_nonneg c]
      have nb : ‖b‖ = 1 := by
        have : ‖b‖ ^ 2 = 1 := by nlinarith
        nlinarith [norm_nonneg b]
      have hd0 : d = 0 := by
        rw [ha0] at e2
        simp only [star_zero, zero_mul, add_zero, zero_add] at e2
        rcases mul_eq_zero.mp e2 with h | h
        · exact absurd (star_eq_zero.mp h) hc0
        · exact h
      refine ⟨0, Complex.arg c, Real.pi, Complex.arg b, ?_⟩
      ext i j
      rw [ZXZ_apply, xRot_apply, E_pi, E_zero]
      cases i <;> cases j
      · simp only [ite_true, ite_false, Bool.false_eq_true]
        rw [← ha, ha0]; ring
      · simp only [ite_true, ite_false, Bool.false_eq_true]
        rw [← hb]
        conv_lhs => rw [polar b, nb]
        push_cast
        ring
      · simp only [ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
        rw [← hc]
        conv_lhs => rw [polar c, nc]
        push_cast
        ring
      · simp only [ite_true]
        rw [← hd, hd0]; ring
    · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      have hale : ‖a‖ ≤ 1 := by nlinarith [sq_nonneg ‖c‖]
      have nb : ‖b‖ = ‖c‖ := by
        have : ‖b‖ ^ 2 = ‖c‖ ^ 2 := by linarith
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
      set θ := Real.arccos ‖a‖ with hθ
      have hcos : Real.cos θ = ‖a‖ := Real.cos_arccos (by linarith) hale
      have hsin : Real.sin θ = ‖c‖ := by
        rw [hθ, Real.sin_arccos]
        have : 1 - ‖a‖ ^ 2 = ‖c‖ ^ 2 := by linarith
        rw [this, Real.sqrt_sq (norm_nonneg _)]
      set A := Complex.arg a
      set B := Complex.arg b
      set C := Complex.arg c
      refine ⟨A - θ, C - A + Real.pi / 2, 2 * θ, B - A + Real.pi / 2, ?_⟩
      ext i j
      rw [ZXZ_apply, xRot_apply]
      cases i <;> cases j
      · simp only [ite_true, ite_false, Bool.false_eq_true]
        rw [← ha, P_eq, hcos]
        conv_lhs => rw [polar a]
        rw [show E (A - θ) * 1 * (E θ * (‖a‖ : ℂ)) * 1 = (‖a‖ : ℂ) * (E (A - θ) * E θ) by ring,
          ← E_add, show A - θ + θ = A by ring]
      · simp only [ite_true, ite_false, Bool.false_eq_true]
        rw [← hb, Q_eq, hsin, ← nb]
        conv_lhs => rw [polar b]
        rw [show E (A - θ) * 1 * (-Complex.I * E θ * (‖b‖ : ℂ)) * E (B - A + Real.pi / 2) =
            -Complex.I * (‖b‖ : ℂ) * (E (A - θ) * E θ * E (B - A + Real.pi / 2)) by ring,
          ← E_add, ← E_add, show A - θ + θ + (B - A + Real.pi / 2) = B + Real.pi / 2 by ring,
          E_add, E_pi_div_two]
        linear_combination ((‖b‖ : ℂ) * E B) * Complex.I_mul_I
      · simp only [ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
        rw [← hc, Q_eq, hsin]
        conv_lhs => rw [polar c]
        rw [show E (A - θ) * E (C - A + Real.pi / 2) * (-Complex.I * E θ * (‖c‖ : ℂ)) * 1 =
            -Complex.I * (‖c‖ : ℂ) * (E (A - θ) * E (C - A + Real.pi / 2) * E θ) by ring,
          ← E_add, ← E_add, show A - θ + (C - A + Real.pi / 2) + θ = C + Real.pi / 2 by ring,
          E_add, E_pi_div_two]
        linear_combination ((‖c‖ : ℂ) * E C) * Complex.I_mul_I
      · simp only [ite_true]
        rw [← hd, P_eq, hcos]
        have hsc : star c ≠ 0 := star_ne_zero.mpr hc0
        apply mul_left_cancel₀ hsc
        have e2' : star c * d = -(star a * b) := by linear_combination e2
        rw [e2', star_polar c, star_polar a]
        conv_lhs => rw [polar b, nb]
        rw [show (‖c‖ : ℂ) * E (-C) * (E (A - θ) * E (C - A + Real.pi / 2) * (E θ * (‖a‖ : ℂ)) *
              E (B - A + Real.pi / 2)) =
            (‖a‖ : ℂ) * (‖c‖ : ℂ) * (E (-C) * E (A - θ) * E (C - A + Real.pi / 2) * E θ *
              E (B - A + Real.pi / 2)) by ring,
          ← E_add, ← E_add, ← E_add, ← E_add,
          show -C + (A - θ) + (C - A + Real.pi / 2) + θ + (B - A + Real.pi / 2) =
            (-A + B) + Real.pi by ring, E_add, E_pi, E_add]
        ring

end Aux_RLexzx

open RotationLadder.Protocol Aux_RLexzx in
theorem solution :
    ∀ U ∈ Matrix.unitaryGroup Bool ℂ, ∃ α β γ κ : ℝ,
      U = Complex.exp (Complex.I * (κ : ℂ)) • (xRot α * zRot β * xRot γ) := by
  intro U hU
  have hstar : star QAlgorithms.hadamard = QAlgorithms.hadamard := by
    ext a b
    rw [Matrix.star_apply]
    cases a <;> cases b <;> simp [QAlgorithms.hadamard, Complex.conj_ofReal]
  have hHmem : QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', hstar, QAlgorithms.hadamard_mul_self]
  have hVmem : QAlgorithms.hadamard * U * QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hHmem hU) hHmem
  obtain ⟨κ, α, β, γ, hV⟩ := zxz _ hVmem
  refine ⟨α, β, γ, κ, ?_⟩
  have hU' : U = QAlgorithms.hadamard * (QAlgorithms.hadamard * U * QAlgorithms.hadamard) * QAlgorithms.hadamard := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, QAlgorithms.hadamard_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, QAlgorithms.hadamard_mul_self, Matrix.mul_one]
  rw [hU', hV]
  simp only [xRot, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
