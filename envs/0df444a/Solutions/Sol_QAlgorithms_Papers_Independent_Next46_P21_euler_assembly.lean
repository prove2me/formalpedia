-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.euler_assembly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:39:49.190974+00:00
-- url     : https://prove2.me/submissions/decbfc5e-2e8a-4835-b9ea-a3a9b0f8881a

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section
open QAlgorithms.Papers.Independent.Next46.P21
open Set
open scoped ComplexConjugate Matrix

theorem g64a_det (A : Matrix Bool Bool ℂ) :
    A.det = A false false * A true true - A false true * A true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm A, Matrix.det_fin_two]
  simp [finTwoEquiv]

theorem g64a_su_struct (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.specialUnitaryGroup Bool ℂ) :
    U true true = conj (U false false) ∧ U false true = -conj (U true false) ∧
    Complex.normSq (U false false) + Complex.normSq (U true false) = 1 := by
  have h2 := Matrix.mem_unitaryGroup_iff'.1 hU.1
  have hdet : U.det = 1 := ((Matrix.mem_specialUnitaryGroup_iff).1 hU).2
  have e3 := congrFun (congrFun h2 false) false
  have e4 := congrFun (congrFun h2 false) true
  rw [g64a_det] at hdet
  simp [Matrix.mul_apply, Fintype.univ_bool, Matrix.star_apply] at e3 e4
  set p := U false false
  set q := U false true
  set r := U true false
  set s := U true true
  have hs : s = conj p := by
    linear_combination (-s) * e3 + (conj p) * hdet + r * e4
  have hq : q = -conj r := by
    linear_combination (-q) * e3 - (conj r) * hdet + p * e4
  refine ⟨hs, hq, ?_⟩
  have : ((Complex.normSq p + Complex.normSq r : ℝ) : ℂ) = 1 := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    linear_combination e3
  exact_mod_cast this

def g64a_D (x xi : ℂ) : Matrix Bool Bool ℂ := Matrix.diagonal fun b => if b then xi else x

theorem g64a_zrot (θ : ℝ) : zRotation θ =
    g64a_D (Complex.exp (-Complex.I * (θ : ℂ) / 2)) (Complex.exp (Complex.I * (θ : ℂ) / 2)) := by
  rfl

theorem g64a_prod (X Xi Y Yi Z Zi : ℂ) :
    g64a_D X Xi * QAlgorithms.hadamard * g64a_D Y Yi * QAlgorithms.hadamard * g64a_D Z Zi =
      fun i j => if i then (if j then Xi * Zi * ((Y + Yi) / 2) else Xi * Z * ((Y - Yi) / 2))
        else (if j then X * Zi * ((Y - Yi) / 2) else X * Z * ((Y + Yi) / 2)) := by
  have hh : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hh2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by rw [sq, hh]
  ext i j
  cases i <;> cases j <;>
    simp [g64a_D, Matrix.mul_apply, Fintype.univ_bool, QAlgorithms.hadamard, Matrix.diagonal] <;>
    (ring_nf; rw [hh2]; ring)

theorem g64a_polar (a : ℂ) : a = (‖a‖ : ℂ) * Complex.exp ((Complex.arg a : ℂ) * Complex.I) :=
  (Complex.norm_mul_exp_arg_mul_I a).symm

theorem g64a_conj_polar (a : ℂ) :
    conj a = (‖a‖ : ℂ) * Complex.exp (-(Complex.arg a : ℂ) * Complex.I) := by
  conv_lhs => rw [g64a_polar a]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

theorem g64a_euler (U : Matrix.specialUnitaryGroup Bool ℂ) : ∃ beta gamma delta : ℝ,
      (U : Matrix Bool Bool ℂ) = zRotation beta * QAlgorithms.hadamard * zRotation gamma *
        QAlgorithms.hadamard * zRotation delta := by
  obtain ⟨hs, hq, hn⟩ := g64a_su_struct U U.2
  set a := (U : Matrix Bool Bool ℂ) false false
  set b := (U : Matrix Bool Bool ℂ) true false
  set A : ℝ := ‖a‖
  set B : ℝ := ‖b‖
  have hAB : A ^ 2 + B ^ 2 = 1 := by
    simpa [A, B, Complex.normSq_eq_norm_sq] using hn
  set y : ℂ := (A : ℂ) - Complex.I * (B : ℂ) with hy
  have hyn : ‖y‖ = 1 := by
    have : Complex.normSq y = 1 := by
      rw [hy, Complex.normSq_apply]; simp; nlinarith
    rw [Complex.normSq_eq_norm_sq] at this
    nlinarith [norm_nonneg y]
  set ψ := Complex.arg y
  have hyexp : Complex.exp ((ψ : ℂ) * Complex.I) = y := by
    have := Complex.norm_mul_exp_arg_mul_I y
    rw [hyn] at this; simpa using this
  have hycexp : Complex.exp (-(ψ : ℂ) * Complex.I) = (A : ℂ) + Complex.I * (B : ℂ) := by
    have := g64a_conj_polar y
    rw [hyn] at this
    simp only [Complex.ofReal_one, one_mul] at this
    rw [← this, hy]
    apply Complex.ext <;> simp
  set ξ : ℝ := (Complex.arg a - Complex.arg b - Real.pi / 2) / 2
  set ζ : ℝ := (Complex.arg a + Complex.arg b + Real.pi / 2) / 2
  refine ⟨-2 * ξ, -2 * ψ, -2 * ζ, ?_⟩
  rw [g64a_zrot, g64a_zrot, g64a_zrot, g64a_prod]
  have c1 : ∀ t : ℝ, -Complex.I * (((-2 * t : ℝ)) : ℂ) / 2 = (t : ℂ) * Complex.I := by
    intro t; push_cast; ring
  have c2 : ∀ t : ℝ, Complex.I * (((-2 * t : ℝ)) : ℂ) / 2 = -(t : ℂ) * Complex.I := by
    intro t; push_cast; ring
  simp only [c1, c2, hyexp, hycexp]
  have hXZ : Complex.exp ((ξ : ℂ) * Complex.I) * Complex.exp ((ζ : ℂ) * Complex.I) =
      Complex.exp ((Complex.arg a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; simp only [ξ, ζ]; push_cast; ring
  have hXZi : Complex.exp (-(ξ : ℂ) * Complex.I) * Complex.exp (-(ζ : ℂ) * Complex.I) =
      Complex.exp (-(Complex.arg a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; simp only [ξ, ζ]; push_cast; ring
  have hXiZ : Complex.exp (-(ξ : ℂ) * Complex.I) * Complex.exp ((ζ : ℂ) * Complex.I) =
      Complex.I * Complex.exp ((Complex.arg b : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    rw [show -(ξ : ℂ) * Complex.I + (ζ : ℂ) * Complex.I =
      (Complex.arg b : ℂ) * Complex.I + (Real.pi : ℂ) / 2 * Complex.I by
        simp only [ξ, ζ]; push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]; ring
  have hXZi' : Complex.exp ((ξ : ℂ) * Complex.I) * Complex.exp (-(ζ : ℂ) * Complex.I) =
      -Complex.I * Complex.exp (-(Complex.arg b : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    rw [show (ξ : ℂ) * Complex.I + -(ζ : ℂ) * Complex.I =
      -(Complex.arg b : ℂ) * Complex.I + -((Real.pi : ℂ) / 2 * Complex.I) by
        simp only [ξ, ζ]; push_cast; ring]
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
  have hy2 : (y + ((A : ℂ) + Complex.I * (B : ℂ))) / 2 = (A : ℂ) := by rw [hy]; ring
  have hy3 : (y - ((A : ℂ) + Complex.I * (B : ℂ))) / 2 = -Complex.I * (B : ℂ) := by rw [hy]; ring
  have hy4 : ((A : ℂ) + Complex.I * (B : ℂ) + y) / 2 = (A : ℂ) := by rw [hy]; ring
  have hy5 : ((A : ℂ) + Complex.I * (B : ℂ) - y) / 2 = Complex.I * (B : ℂ) := by rw [hy]; ring
  ext i j
  cases i <;> cases j
  · simp only [Bool.false_eq_true, if_false, hy2, hy3, hy4, hy5]
    change a = _
    refine (g64a_polar a).trans ?_
    rw [hXZ]; ring
  · simp only [Bool.false_eq_true, if_false, if_true, hy2, hy3, hy4, hy5]
    rw [hq, g64a_conj_polar b, hXZi']
    first
    | linear_combination ((B : ℂ) * Complex.exp (-(Complex.arg b : ℂ) * Complex.I)) * Complex.I_sq
    | linear_combination (-(B : ℂ) * Complex.exp (-(Complex.arg b : ℂ) * Complex.I)) * Complex.I_sq
  · simp only [Bool.false_eq_true, if_false, if_true, hy2, hy3, hy4, hy5]
    change b = _
    refine (g64a_polar b).trans ?_
    rw [hXiZ]
    first
    | linear_combination ((B : ℂ) * Complex.exp ((Complex.arg b : ℂ) * Complex.I)) * Complex.I_sq
    | linear_combination (-(B : ℂ) * Complex.exp ((Complex.arg b : ℂ) * Complex.I)) * Complex.I_sq
  · simp only [if_true, hy2, hy3, hy4, hy5]
    rw [hs, g64a_conj_polar a, hXZi]
    ring

open scoped Matrix.Norms.L2Operator

theorem g64a_unorm (V : Matrix Bool Bool ℂ) (hV : star V * V = 1) : ‖V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [← Matrix.star_eq_conjTranspose, hV, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal,
    pi_norm_const, norm_one] at h
  nlinarith [norm_nonneg V]

theorem g64a_had : ‖QAlgorithms.hadamard‖ ≤ 1 := by
  apply g64a_unorm
  have hh : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Fintype.univ_bool, QAlgorithms.hadamard, Matrix.star_apply,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_neg]
  all_goals first | (rw [hr]; norm_num) | linarith [hr]

theorem g64a_zr (θ : ℝ) : ‖zRotation θ‖ ≤ 1 := by
  rw [zRotation, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
  cases b <;> simp [zPhase, Complex.norm_exp]

theorem g64a_p5 (a b c d e : Matrix Bool Bool ℂ) :
    ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  calc ‖a * b * c * d * e‖ ≤ ‖a * b * c * d‖ * ‖e‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖a * b * c‖ * ‖d‖ * ‖e‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ ‖a * b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _

theorem g64a_err (beta gamma delta eps : ℝ) (A B D : Matrix.unitaryGroup Bool ℂ)
    (hA : QAlgorithms.specNorm ((A : Matrix Bool Bool ℂ) - zRotation beta) ≤ eps / 3)
    (hB : QAlgorithms.specNorm ((B : Matrix Bool Bool ℂ) - zRotation gamma) ≤ eps / 3)
    (hD : QAlgorithms.specNorm ((D : Matrix Bool Bool ℂ) - zRotation delta) ≤ eps / 3) :
    QAlgorithms.specNorm ((A : Matrix Bool Bool ℂ) * QAlgorithms.hadamard *
          (B : Matrix Bool Bool ℂ) * QAlgorithms.hadamard * (D : Matrix Bool Bool ℂ) -
          zRotation beta * QAlgorithms.hadamard * zRotation gamma *
        QAlgorithms.hadamard * zRotation delta) ≤ eps := by
  unfold QAlgorithms.specNorm at *
  set H := QAlgorithms.hadamard
  have hBn : ‖(B : Matrix Bool Bool ℂ)‖ ≤ 1 := g64a_unorm _ (Matrix.mem_unitaryGroup_iff'.1 B.2)
  have hDn : ‖(D : Matrix Bool Bool ℂ)‖ ≤ 1 := g64a_unorm _ (Matrix.mem_unitaryGroup_iff'.1 D.2)
  have he : 0 ≤ eps / 3 := le_trans (norm_nonneg _) hA
  have hH := g64a_had
  have hb := g64a_zr beta
  have hg := g64a_zr gamma
  have e : (A : Matrix Bool Bool ℂ) * H * (B : Matrix Bool Bool ℂ) * H * (D : Matrix Bool Bool ℂ) -
      zRotation beta * H * zRotation gamma * H * zRotation delta =
      ((A : Matrix Bool Bool ℂ) - zRotation beta) * H * (B : Matrix Bool Bool ℂ) * H *
        (D : Matrix Bool Bool ℂ) +
      zRotation beta * H * ((B : Matrix Bool Bool ℂ) - zRotation gamma) * H *
        (D : Matrix Bool Bool ℂ) +
      zRotation beta * H * zRotation gamma * H * ((D : Matrix Bool Bool ℂ) - zRotation delta) := by
    simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
  rw [e]
  have t1 := g64a_p5 ((A : Matrix Bool Bool ℂ) - zRotation beta) H (B : Matrix Bool Bool ℂ) H
    (D : Matrix Bool Bool ℂ)
  have t2 := g64a_p5 (zRotation beta) H ((B : Matrix Bool Bool ℂ) - zRotation gamma) H
    (D : Matrix Bool Bool ℂ)
  have t3 := g64a_p5 (zRotation beta) H (zRotation gamma) H
    ((D : Matrix Bool Bool ℂ) - zRotation delta)
  have u1 : ‖(A : Matrix Bool Bool ℂ) - zRotation beta‖ * ‖H‖ * ‖(B : Matrix Bool Bool ℂ)‖ *
      ‖H‖ * ‖(D : Matrix Bool Bool ℂ)‖ ≤ eps / 3 * 1 * 1 * 1 * 1 := by gcongr <;> linarith
  have u2 : ‖zRotation beta‖ * ‖H‖ * ‖(B : Matrix Bool Bool ℂ) - zRotation gamma‖ * ‖H‖ *
      ‖(D : Matrix Bool Bool ℂ)‖ ≤ 1 * 1 * (eps / 3) * 1 * 1 := by gcongr <;> linarith
  have u3 : ‖zRotation beta‖ * ‖H‖ * ‖zRotation gamma‖ * ‖H‖ *
      ‖(D : Matrix Bool Bool ℂ) - zRotation delta‖ ≤ 1 * 1 * 1 * 1 * (eps / 3) := by gcongr <;> linarith
  calc _ ≤ _ := norm_add₃_le
    _ ≤ eps := by linarith

theorem g64a_words (a b d : List Letter) :
      wordMatrix (assemble a b d) = wordMatrix a * QAlgorithms.hadamard * wordMatrix b *
        QAlgorithms.hadamard * wordMatrix d ∧
      tCount (assemble a b d) = tCount a + tCount b + tCount d := by
  constructor
  · simp [assemble, wordMatrix, List.reverse_append, List.prod_append, letterMatrix,
      Matrix.mul_assoc]
  · simp [assemble, tCount, List.filter_append]
    omega

theorem solution :
    (∀ U : Matrix.specialUnitaryGroup Bool ℂ, ∃ beta gamma delta : ℝ,
      (U : Matrix Bool Bool ℂ) = zRotation beta * QAlgorithms.hadamard * zRotation gamma *
        QAlgorithms.hadamard * zRotation delta ∧
      ∀ eps : ℝ, 0 < eps → ∀ A B D : Matrix.unitaryGroup Bool ℂ,
        QAlgorithms.specNorm ((A : Matrix Bool Bool ℂ) - zRotation beta) ≤ eps / 3 →
        QAlgorithms.specNorm ((B : Matrix Bool Bool ℂ) - zRotation gamma) ≤ eps / 3 →
        QAlgorithms.specNorm ((D : Matrix Bool Bool ℂ) - zRotation delta) ≤ eps / 3 →
        QAlgorithms.specNorm ((A : Matrix Bool Bool ℂ) * QAlgorithms.hadamard *
          (B : Matrix Bool Bool ℂ) * QAlgorithms.hadamard * (D : Matrix Bool Bool ℂ) -
          (U : Matrix Bool Bool ℂ)) ≤ eps) ∧
    (∀ a b d : List Letter,
      wordMatrix (assemble a b d) = wordMatrix a * QAlgorithms.hadamard * wordMatrix b *
        QAlgorithms.hadamard * wordMatrix d ∧
      tCount (assemble a b d) = tCount a + tCount b + tCount d) := by
  refine ⟨fun U => ?_, g64a_words⟩
  obtain ⟨β, γ, δ, h⟩ := g64a_euler U
  refine ⟨β, γ, δ, h, fun eps _ A B D hA hB hD => ?_⟩
  rw [h]
  exact g64a_err β γ δ eps A B D hA hB hD
