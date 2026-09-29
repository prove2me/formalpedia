-- Prove2me | solution 1 for SiegelFields.su2_double_cover_so3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:01:08.934697+00:00
-- url     : https://prove2.me/submissions/22cdfa9a-19eb-4242-9e44-9dc4c7dfac39

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex


namespace SiegelFields

lemma sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact_mod_cast this

lemma sqrt2_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast this

lemma vtm_eq (v : Fin 3 → ℝ) : vecToMatrix v =
    !![(Real.sqrt 2 : ℂ)⁻¹ * v 0, (Real.sqrt 2 : ℂ)⁻¹ * (v 1 - I * v 2);
       (Real.sqrt 2 : ℂ)⁻¹ * (v 1 + I * v 2), -((Real.sqrt 2 : ℂ)⁻¹ * v 0)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vecToMatrix]

lemma vtm_isThreeVector (v : Fin 3 → ℝ) : IsThreeVector (vecToMatrix v) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vtm_eq, Matrix.conjTranspose_apply, Complex.ext_iff] <;> ring
  · simp [vtm_eq, Matrix.trace_fin_two]

lemma vtm_injective : Function.Injective vecToMatrix := by
  intro v w h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [vtm_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
  have hs := sqrt2_ne
  have e0 : (v 0 : ℂ) = w 0 := by
    have := mul_left_cancel₀ (inv_ne_zero hs) h00; exact this
  have e1 : ((v 1 : ℂ) - I * v 2) = (w 1 - I * w 2) := mul_left_cancel₀ (inv_ne_zero hs) h01
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  simp at r1 i1
  funext i
  fin_cases i
  · exact_mod_cast e0
  · simpa using r1
  · simpa using i1

theorem m1 (V : Matrix (Fin 2) (Fin 2) ℂ) :
    IsThreeVector V ↔ ∃! v : Fin 3 → ℝ, V = vecToMatrix v := by
  constructor
  · rintro ⟨hH, hT⟩
    have h00 : star (V 0 0) = V 0 0 := by simpa using congrFun (congrFun hH 0) 0
    have h10 : star (V 0 1) = V 1 0 := by simpa using congrFun (congrFun hH 1) 0
    have h11 : V 1 1 = -V 0 0 := by
      rw [Matrix.trace_fin_two] at hT; linear_combination hT
    have him : (V 0 0).im = 0 := by
      have := congrArg Complex.im h00; simp at this; linarith
    refine ⟨![Real.sqrt 2 * (V 0 0).re, Real.sqrt 2 * (V 0 1).re,
      -(Real.sqrt 2 * (V 0 1).im)], ?_, fun w hw => vtm_injective ?_⟩
    · have hs : Real.sqrt 2 ≠ 0 := by positivity
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [vtm_eq, Complex.ext_iff, ← h10, h11, him] <;> field_simp <;>
          (try simp [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])
    · rw [← hw]
      have hs : Real.sqrt 2 ≠ 0 := by positivity
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [vtm_eq, Complex.ext_iff, ← h10, h11, him] <;> field_simp <;>
          (try simp [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])
  · rintro ⟨v, rfl, -⟩
    exact vtm_isThreeVector v

theorem m2 (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : IsThreeVector V) :
    IsThreeVector (U * V * Uᴴ) ∧ (U * V * Uᴴ).det = V.det := by
  have hUU : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU; simpa [Matrix.star_eq_conjTranspose] using this
  have hUU' : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU; simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hV.1.eq, Matrix.mul_assoc]
  · rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, hV.2]
  · rw [Matrix.det_mul, Matrix.det_mul, mul_comm (U.det), mul_assoc, ← Matrix.det_mul, hUU',
      Matrix.det_one, mul_one]


lemma unitary_left {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Uᴴ * U = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hU; simpa [Matrix.star_eq_conjTranspose] using this

lemma unitary_right {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U * Uᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp hU; simpa [Matrix.star_eq_conjTranspose] using this

lemma vtm_lin (v : Fin 3 → ℝ) : vecToMatrix v = ∑ j, (v j : ℂ) • basisMatrix j := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [basisMatrix, vtm_eq, Fin.sum_univ_three, Pi.single_apply] <;> ring

lemma coord (i : Fin 3) (v : Fin 3 → ℝ) : (trace (basisMatrix i * vecToMatrix v)).re = v i := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  fin_cases i
  · simp [basisMatrix, vtm_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Pi.single_apply]; field_simp; linear_combination 2 * (v 0) * h2
  · simp [basisMatrix, vtm_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Pi.single_apply]; field_simp; linear_combination 2 * (v 1) * h2
  · simp [basisMatrix, vtm_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Pi.single_apply]; field_simp; linear_combination 2 * (v 2) * h2

theorem m4 (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (v : Fin 3 → ℝ) :
    U * vecToMatrix v * Uᴴ = vecToMatrix (rotationOf U *ᵥ v) := by
  obtain ⟨w, hw, -⟩ := (m1 _).mp (m2 U hU _ (vtm_isThreeVector v)).1
  rw [hw]
  congr 1
  funext i
  have hc := coord i w
  rw [← hw] at hc
  rw [← hc]
  simp only [Matrix.mulVec, dotProduct, rotationOf, Matrix.of_apply]
  rw [vtm_lin v]
  have hterm : ∀ j, basisMatrix i * (U * ((v j : ℂ) • basisMatrix j) * Uᴴ) =
      (v j : ℂ) • (basisMatrix i * U * basisMatrix j * Uᴴ) := by
    intro j
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum]
  simp only [hterm, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, smul_eq_mul,
    Complex.re_ofReal_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem m3 (U W : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V → U * V * Uᴴ = W * V * Wᴴ) ↔
      W = U ∨ W = -U := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU hW
  have hUU := unitary_left hU.1
  have hWW := unitary_left hW.1
  have hWW' := unitary_right hW.1
  constructor
  · intro h
    set X := Wᴴ * U with hX
    have hcomm : ∀ V, IsThreeVector V → X * V = V * X := by
      intro V hV
      have e1 : Wᴴ * (U * V * Uᴴ) * U = X * V := by
        rw [hX]; simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]
      have e2 : Wᴴ * (W * V * Wᴴ) * U = V * X := by
        rw [hX]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul]
      rw [← e1, ← e2, h V hV]
    have hs : ((Real.sqrt 2 : ℂ))⁻¹ ≠ 0 := inv_ne_zero sqrt2_ne
    have c0 := hcomm _ (vtm_isThreeVector (Pi.single 0 1))
    have c1 := hcomm _ (vtm_isThreeVector (Pi.single 1 1))
    have q01 := congrFun (congrFun c0 0) 1
    have q10 := congrFun (congrFun c0 1) 0
    have q01' := congrFun (congrFun c1 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, vtm_eq, Pi.single_apply] at q01 q10 q01'
    have x01 : X 0 1 = 0 := by
      have : (2 * (Real.sqrt 2 : ℂ)⁻¹) * X 0 1 = 0 := by linear_combination -q01
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (mul_ne_zero two_ne_zero hs)
      · exact h0
    have x10 : X 1 0 = 0 := by
      have : (2 * (Real.sqrt 2 : ℂ)⁻¹) * X 1 0 = 0 := by linear_combination q10
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (mul_ne_zero two_ne_zero hs)
      · exact h0
    have x11 : X 1 1 = X 0 0 := by
      have : (Real.sqrt 2 : ℂ)⁻¹ * (X 1 1 - X 0 0) = 0 := by linear_combination -q01'
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hs
      · linear_combination h0
    have hXc : X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext a b; fin_cases a <;> fin_cases b <;> simp [x01, x10, x11]
    have hdet : X.det = 1 := by
      rw [hX, Matrix.det_mul, Matrix.det_conjTranspose, hW.2, hU.2]; simp
    have hsq : X 0 0 * X 0 0 = 1 := by
      rw [Matrix.det_fin_two, x01, x10, x11] at hdet; linear_combination hdet
    have hUX : U = X 0 0 • W := by
      calc U = W * X := by rw [hX, ← Matrix.mul_assoc, hWW', Matrix.one_mul]
        _ = X 0 0 • W := by conv_lhs => rw [hXc]
                            rw [Matrix.mul_smul, Matrix.mul_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left; rw [hUX, h1, one_smul]
    · right; rw [hUX, h1, neg_one_smul, neg_neg]
  · rintro (rfl | rfl) V _
    · rfl
    · simp [Matrix.conjTranspose_neg]


/-- The SU(2) matrix with first column `(a + b i, c + d i)`. -/
def qU (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨a, b⟩, -(starRingEnd ℂ) ⟨c, d⟩; ⟨c, d⟩, (starRingEnd ℂ) ⟨a, b⟩]

lemma qU_H (a b c d : ℝ) : (qU a b c d)ᴴ =
    !![(starRingEnd ℂ) ⟨a, b⟩, (starRingEnd ℂ) ⟨c, d⟩; -⟨c, d⟩, ⟨a, b⟩] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qU, Matrix.conjTranspose_apply]

def rotP (a b c d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a^2 + b^2 - c^2 - d^2, -2*a*c + 2*b*d, -2*a*d - 2*b*c;
     2*a*c + 2*b*d, a^2 - b^2 - c^2 + d^2, 2*a*b - 2*c*d;
     2*a*d - 2*b*c, -2*a*b - 2*c*d, a^2 - b^2 + c^2 - d^2]

lemma basis_eq : ∀ i : Fin 3, basisMatrix i =
    ![!![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), 0; 0, -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)],
      !![0, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ); (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), 0],
      !![0, -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * I); (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * I, 0]] i := by
  intro i
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [basisMatrix, vtm_eq] <;> ring

lemma rot_qU (a b c d : ℝ) : rotationOf (qU a b c d) = rotP a b c d := by
  set t : ℝ := (Real.sqrt 2)⁻¹ with ht
  have h2 : 2 * t ^ 2 = 1 := by
    rw [ht, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have key : ∀ i j, rotationOf (qU a b c d) i j = 2 * t ^ 2 * rotP a b c d i j := by
    intro i j
    simp only [rotationOf, Matrix.of_apply, basis_eq, qU_H]
    fin_cases i <;> fin_cases j <;>
      simp [qU, rotP, Matrix.mul_fin_two, Matrix.trace_fin_two, ← ht] <;> ring
  ext i j
  rw [key, h2, one_mul]


lemma su2_eq_qU (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U = qU (U 0 0).re (U 0 0).im (U 1 0).re (U 1 0).im ∧
      (U 0 0).re ^ 2 + (U 0 0).im ^ 2 + (U 1 0).re ^ 2 + (U 1 0).im ^ 2 = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU
  have hUU' := unitary_right hU.1
  have hadj : Uᴴ = Matrix.adjugate U := by
    calc Uᴴ = (Matrix.adjugate U * U) * Uᴴ := by rw [Matrix.adjugate_mul, hU.2, one_smul, Matrix.one_mul]
      _ = Matrix.adjugate U := by rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] at e00 e01
  have hdet := hU.2
  rw [Matrix.det_fin_two] at hdet
  have h11 : U 1 1 = (starRingEnd ℂ) (U 0 0) := e00.symm
  have h01 : U 0 1 = -(starRingEnd ℂ) (U 1 0) := by linear_combination e01
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [qU, h11, h01]
  · rw [h11, h01] at hdet
    have := congrArg Complex.re hdet
    simp at this
    linarith

lemma qU_mem {a b c d : ℝ} (hn : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    qU a b c d ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff,
    Matrix.star_eq_conjTranspose, qU_H]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qU, Matrix.mul_fin_two, Complex.ext_iff] <;> (try refine ⟨?_, ?_⟩) <;>
      first | trivial | ring1 | linear_combination hn |
        linear_combination (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 1) * hn
  · simp [qU, Matrix.det_fin_two, Complex.ext_iff]
    constructor
    · linear_combination hn
    · ring

lemma rotP_mem {a b c d : ℝ} (hn : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    rotP a b c d ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotP, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 1) * hn
  · simp [rotP, Matrix.det_fin_three]
    linear_combination ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      + 1) * hn

def Mq (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 + R 0 0 + R 1 1 + R 2 2, R 1 2 - R 2 1, R 1 0 - R 0 1, R 2 0 - R 0 2;
     R 1 2 - R 2 1, 1 + R 0 0 - R 1 1 - R 2 2, -(R 0 2 + R 2 0), R 0 1 + R 1 0;
     R 1 0 - R 0 1, -(R 0 2 + R 2 0), 1 - R 0 0 - R 1 1 + R 2 2, -(R 1 2 + R 2 1);
     R 2 0 - R 0 2, R 0 1 + R 1 0, -(R 1 2 + R 2 1), 1 - R 0 0 + R 1 1 - R 2 2]

lemma Mq_00 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 0 0 = 1 + R 0 0 + R 1 1 + R 2 2 := rfl
lemma Mq_01 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 0 1 = R 1 2 - R 2 1 := rfl
lemma Mq_02 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 0 2 = R 1 0 - R 0 1 := rfl
lemma Mq_03 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 0 3 = R 2 0 - R 0 2 := rfl
lemma Mq_10 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 1 0 = R 1 2 - R 2 1 := rfl
lemma Mq_11 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 1 1 = 1 + R 0 0 - R 1 1 - R 2 2 := rfl
lemma Mq_12 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 1 2 = -(R 0 2 + R 2 0) := rfl
lemma Mq_13 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 1 3 = R 0 1 + R 1 0 := rfl
lemma Mq_20 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 2 0 = R 1 0 - R 0 1 := rfl
lemma Mq_21 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 2 1 = -(R 0 2 + R 2 0) := rfl
lemma Mq_22 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 2 2 = 1 - R 0 0 - R 1 1 + R 2 2 := rfl
lemma Mq_23 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 2 3 = -(R 1 2 + R 2 1) := rfl
lemma Mq_30 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 3 0 = R 2 0 - R 0 2 := rfl
lemma Mq_31 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 3 1 = R 0 1 + R 1 0 := rfl
lemma Mq_32 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 3 2 = -(R 1 2 + R 2 1) := rfl
lemma Mq_33 (R : Matrix (Fin 3) (Fin 3) ℝ) : Mq R 3 3 = 1 - R 0 0 + R 1 1 - R 2 2 := rfl

lemma su2_surj (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, rotationOf U = R := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hR
  obtain ⟨hO, hdet⟩ := hR
  have hRRt : R * Rᵀ = 1 := by
    have h := hO; rw [Matrix.mem_orthogonalGroup_iff] at h; exact h
  have hRtR : Rᵀ * R = 1 := by
    have h := hO; rw [Matrix.mem_orthogonalGroup_iff'] at h; exact h
  have hadj : Rᵀ = Matrix.adjugate R := by
    calc Rᵀ = (Matrix.adjugate R * R) * Rᵀ := by
          rw [Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mul]
      _ = Matrix.adjugate R := by rw [Matrix.mul_assoc, hRRt, Matrix.mul_one]
  have hO1_00 : (R 0 0)^2 + (R 0 1)^2 + (R 0 2)^2 - 1 = 0 := by
    have h := congrFun (congrFun hRRt 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO2_00 : (R 0 0)^2 + (R 1 0)^2 + (R 2 0)^2 - 1 = 0 := by
    have h := congrFun (congrFun hRtR 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_00 : (R 0 0) - (R 1 1)*(R 2 2) + (R 1 2)*(R 2 1) = 0 := by
    have h := congrFun (congrFun hadj 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO1_01 : (R 0 0)*(R 1 0) + (R 0 1)*(R 1 1) + (R 0 2)*(R 1 2) = 0 := by
    have h := congrFun (congrFun hRRt 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO2_01 : (R 0 0)*(R 0 1) + (R 1 0)*(R 1 1) + (R 2 0)*(R 2 1) = 0 := by
    have h := congrFun (congrFun hRtR 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_01 : (R 0 1)*(R 2 2) - (R 0 2)*(R 2 1) + (R 1 0) = 0 := by
    have h := congrFun (congrFun hadj 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO1_02 : (R 0 0)*(R 2 0) + (R 0 1)*(R 2 1) + (R 0 2)*(R 2 2) = 0 := by
    have h := congrFun (congrFun hRRt 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO2_02 : (R 0 0)*(R 0 2) + (R 1 0)*(R 1 2) + (R 2 0)*(R 2 2) = 0 := by
    have h := congrFun (congrFun hRtR 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_02 : -(R 0 1)*(R 1 2) + (R 0 2)*(R 1 1) + (R 2 0) = 0 := by
    have h := congrFun (congrFun hadj 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_10 : (R 0 1) + (R 1 0)*(R 2 2) - (R 1 2)*(R 2 0) = 0 := by
    have h := congrFun (congrFun hadj 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO1_11 : (R 1 0)^2 + (R 1 1)^2 + (R 1 2)^2 - 1 = 0 := by
    have h := congrFun (congrFun hRRt 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO2_11 : (R 0 1)^2 + (R 1 1)^2 + (R 2 1)^2 - 1 = 0 := by
    have h := congrFun (congrFun hRtR 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_11 : -(R 0 0)*(R 2 2) + (R 0 2)*(R 2 0) + (R 1 1) = 0 := by
    have h := congrFun (congrFun hadj 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO1_12 : (R 1 0)*(R 2 0) + (R 1 1)*(R 2 1) + (R 1 2)*(R 2 2) = 0 := by
    have h := congrFun (congrFun hRRt 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO2_12 : (R 0 1)*(R 0 2) + (R 1 1)*(R 1 2) + (R 2 1)*(R 2 2) = 0 := by
    have h := congrFun (congrFun hRtR 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_12 : (R 0 0)*(R 1 2) - (R 0 2)*(R 1 0) + (R 2 1) = 0 := by
    have h := congrFun (congrFun hadj 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_20 : (R 0 2) - (R 1 0)*(R 2 1) + (R 1 1)*(R 2 0) = 0 := by
    have h := congrFun (congrFun hadj 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_21 : (R 0 0)*(R 2 1) - (R 0 1)*(R 2 0) + (R 1 2) = 0 := by
    have h := congrFun (congrFun hadj 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO1_22 : (R 2 0)^2 + (R 2 1)^2 + (R 2 2)^2 - 1 = 0 := by
    have h := congrFun (congrFun hRRt 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hO2_22 : (R 0 2)^2 + (R 1 2)^2 + (R 2 2)^2 - 1 = 0 := by
    have h := congrFun (congrFun hRtR 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hC_22 : -(R 0 0)*(R 1 1) + (R 0 1)*(R 1 0) + (R 2 2) = 0 := by
    have h := congrFun (congrFun hadj 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, Matrix.one_apply] at h
    linear_combination h
  have hrank : ∀ i j k : Fin 4, Mq R i k * Mq R j k = Mq R i j * Mq R k k := by
    intro i j k
    match i, j, k with
    | 0, 0, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 0, 0, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO2_00 + (-2) * hC_00 + (1) * hO1_11 + (1) * hO1_22
    | 0, 0, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO2_00 + (1) * hO2_11 + (-1) * hO1_22 + (-2) * hC_22
    | 0, 0, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_00 + (-1) * hO2_11 + (-2) * hC_11 + (1) * hO1_22
    | 0, 1, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 0, 1, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 0, 1, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_12 + (1) * hO2_12 + (1) * hC_12 + (-1) * hC_21
    | 0, 1, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_12 + (-1) * hO2_12 + (1) * hC_12 + (-1) * hC_21
    | 0, 2, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 0, 2, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_01 + (1) * hO2_01 + (-1) * hC_01 + (1) * hC_10
    | 0, 2, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 0, 2, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_01 + (-1) * hO2_01 + (-1) * hC_01 + (1) * hC_10
    | 0, 3, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 0, 3, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_02 + (1) * hO2_02 + (-1) * hC_02 + (1) * hC_20
    | 0, 3, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_02 + (-1) * hO2_02 + (-1) * hC_02 + (1) * hC_20
    | 0, 3, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 0, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 0, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 0, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_12 + (1) * hO2_12 + (1) * hC_12 + (-1) * hC_21
    | 1, 0, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_12 + (-1) * hO2_12 + (1) * hC_12 + (-1) * hC_21
    | 1, 1, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO2_00 + (-2) * hC_00 + (1) * hO1_11 + (1) * hO1_22
    | 1, 1, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 1, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_00 + (-1) * hO2_11 + (2) * hC_11 + (1) * hO1_22
    | 1, 1, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO2_00 + (1) * hO2_11 + (-1) * hO1_22 + (2) * hC_22
    | 1, 2, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_02 + (1) * hO2_02 + (1) * hC_02 + (1) * hC_20
    | 1, 2, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 2, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 2, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_02 + (-1) * hO2_02 + (1) * hC_02 + (1) * hC_20
    | 1, 3, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_01 + (-1) * hO2_01 + (-1) * hC_01 + (-1) * hC_10
    | 1, 3, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 1, 3, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_01 + (1) * hO2_01 + (-1) * hC_01 + (-1) * hC_10
    | 1, 3, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 0, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 0, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_01 + (1) * hO2_01 + (-1) * hC_01 + (1) * hC_10
    | 2, 0, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 0, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_01 + (-1) * hO2_01 + (-1) * hC_01 + (1) * hC_10
    | 2, 1, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_02 + (1) * hO2_02 + (1) * hC_02 + (1) * hC_20
    | 2, 1, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 1, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 1, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_02 + (-1) * hO2_02 + (1) * hC_02 + (1) * hC_20
    | 2, 2, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO2_00 + (1) * hO2_11 + (-1) * hO1_22 + (-2) * hC_22
    | 2, 2, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_00 + (-1) * hO2_11 + (2) * hC_11 + (1) * hO1_22
    | 2, 2, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 2, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO2_00 + (2) * hC_00 + (1) * hO1_11 + (1) * hO1_22
    | 2, 3, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_12 + (1) * hO2_12 + (1) * hC_12 + (1) * hC_21
    | 2, 3, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_12 + (-1) * hO2_12 + (1) * hC_12 + (1) * hC_21
    | 2, 3, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 2, 3, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 0, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 0, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_02 + (1) * hO2_02 + (-1) * hC_02 + (1) * hC_20
    | 3, 0, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_02 + (-1) * hO2_02 + (-1) * hC_02 + (1) * hC_20
    | 3, 0, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 1, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_01 + (-1) * hO2_01 + (-1) * hC_01 + (-1) * hC_10
    | 3, 1, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 1, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_01 + (1) * hO2_01 + (-1) * hC_01 + (-1) * hC_10
    | 3, 1, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 2, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_12 + (1) * hO2_12 + (1) * hC_12 + (1) * hC_21
    | 3, 2, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO1_12 + (-1) * hO2_12 + (1) * hC_12 + (1) * hC_21
    | 3, 2, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 2, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
    | 3, 3, 0 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO1_00 + (-1) * hO2_11 + (-2) * hC_11 + (1) * hO1_22
    | 3, 3, 1 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (1) * hO2_00 + (1) * hO2_11 + (-1) * hO1_22 + (2) * hC_22
    | 3, 3, 2 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> linear_combination (-1) * hO2_00 + (2) * hC_00 + (1) * hO1_11 + (1) * hO1_22
    | 3, 3, 3 => simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] <;> ring
  obtain ⟨k, hk⟩ : ∃ k, 0 < Mq R k k := by
    by_contra h
    push_neg at h
    have hsum : Mq R 0 0 + Mq R 1 1 + Mq R 2 2 + Mq R 3 3 = 4 := by
      simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33]; ring
    linarith [h 0, h 1, h 2, h 3]
  set s := Real.sqrt (Mq R k k) with hsdef
  have hs : s * s = Mq R k k := Real.mul_self_sqrt hk.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hk
  set q : Fin 4 → ℝ := fun i => Mq R i k / (2 * s) with hqdef
  have hq : ∀ i j, q i * q j = Mq R i j / 4 := by
    intro i j
    calc q i * q j = (Mq R i k * Mq R j k) / (4 * (s * s)) := by
          simp only [hqdef]; field_simp; ring
      _ = (Mq R i j * Mq R k k) / (4 * Mq R k k) := by rw [hrank, hs]
      _ = Mq R i j / 4 := by field_simp
  have hsum : Mq R 0 0 + Mq R 1 1 + Mq R 2 2 + Mq R 3 3 = 4 := by
      simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33]; ring
  have hn : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1 := by
    linear_combination hq 0 0 + hq 1 1 + hq 2 2 + hq 3 3 + hsum / 4
  refine ⟨qU (q 0) (q 1) (q 2) (q 3), qU_mem hn, ?_⟩
  rw [rot_qU]
  have q00 := hq 0 0
  have q11 := hq 1 1
  have q22 := hq 2 2
  have q33 := hq 3 3
  have q01 := hq 0 1
  have q02 := hq 0 2
  have q03 := hq 0 3
  have q12 := hq 1 2
  have q13 := hq 1 3
  have q23 := hq 2 3
  simp only [Mq_00, Mq_01, Mq_02, Mq_03, Mq_10, Mq_11, Mq_12, Mq_13, Mq_20, Mq_21, Mq_22, Mq_23, Mq_30, Mq_31, Mq_32, Mq_33] at q00 q11 q22 q33 q01 q02 q03 q12 q13 q23
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotP]
  · linear_combination q00 + q11 - q22 - q33
  · linear_combination -2 * q02 + 2 * q13
  · linear_combination -2 * q03 - 2 * q12
  · linear_combination 2 * q02 + 2 * q13
  · linear_combination q00 - q11 - q22 + q33
  · linear_combination 2 * q01 - 2 * q23
  · linear_combination 2 * q03 - 2 * q12
  · linear_combination -2 * q01 - 2 * q23
  · linear_combination q00 - q11 + q22 - q33

theorem goal_main :
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf (U * W) = rotationOf U * rotationOf W) ∧
    (∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∃ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, rotationOf U = R) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U = rotationOf W ↔ W = U ∨ W = -U) := by
  refine ⟨?_, ?_, su2_surj, ?_⟩
  · intro U hU
    obtain ⟨hform, hn⟩ := su2_eq_qU U hU
    rw [hform, rot_qU]
    exact rotP_mem hn
  · intro U hU W hW
    have hU1 := (Matrix.mem_specialUnitaryGroup_iff.mp hU).1
    have hW1 := (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
    have hUW : U * W ∈ Matrix.unitaryGroup (Fin 2) ℂ := Submonoid.mul_mem _ hU1 hW1
    have key : ∀ v, rotationOf (U * W) *ᵥ v = (rotationOf U * rotationOf W) *ᵥ v := by
      intro v
      apply vtm_injective
      rw [← m4 _ hUW, ← Matrix.mulVec_mulVec, ← m4 U hU1, ← m4 W hW1,
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · intro U hU W hW
    have hU1 := (Matrix.mem_specialUnitaryGroup_iff.mp hU).1
    have hW1 := (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
    constructor
    · intro h
      apply (m3 U W hU hW).mp
      intro V hV
      obtain ⟨v, rfl, -⟩ := (m1 V).mp hV
      rw [m4 U hU1, m4 W hW1, h]
    · rintro (rfl | rfl)
      · rfl
      · ext i j
        simp [rotationOf, Matrix.conjTranspose_neg]

end SiegelFields

open SiegelFields

theorem solution :
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf (U * W) = rotationOf U * rotationOf W) ∧
    (∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∃ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, rotationOf U = R) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U = rotationOf W ↔ W = U ∨ W = -U) := by
  exact goal_main
