-- Prove2me | solution 1 for QAlgorithms.Nannicini.groverOperator_eigenstates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:29:14.106696+00:00
-- url     : https://prove2.me/submissions/ae30b9fa-c1a4-4ab6-8886-2ed5c4bcf290

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

open QAlgorithms
open scoped ComplexConjugate

private lemma aa_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  ext i
  exact (congrFun (Matrix.mulVec_mulVec (WithLp.ofLp v) A B) i).symm

private lemma aa_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (u v : EuclideanSpace ℂ ι) : act A (u + v) = act A u + act A v := by
  ext i
  simp [act, Matrix.mulVec_add]

private lemma aa_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (u v : EuclideanSpace ℂ ι) : act A (u - v) = act A u - act A v := by
  ext i
  simp [act, Matrix.mulVec_sub]

private lemma aa_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (v : EuclideanSpace ℂ ι) : act A (c • v) = c • act A v := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

private lemma aa_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) : act (1 : Matrix ι ι ℂ) v = v := by
  ext i
  simp [act]

private lemma aa_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ι) : act A (ket z) = WithLp.toLp 2 (fun i => A i z) := by
  ext i
  simp [act, ket]

private lemma aa_refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι) (v : EuclideanSpace ℂ ι) :
    act (reflAt z) v = (2 * v z) • ket z - v := by
  ext i
  simp only [act, reflAt, Matrix.mulVec_diagonal, PiLp.toLp_apply,
    ket]
  by_cases h : i = z
  · subst i; simp; ring
  · simp [h]

private lemma aa_reflect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (z : ι)
    (v : EuclideanSpace ℂ ι) :
    act (A * reflAt z * star A) v =
      (2 * inner ℂ (act A (ket z)) v) • act A (ket z) - v := by
  have hc : (act (star A) v) z = inner ℂ (act A (ket z)) v := by
    rw [aa_ket]
    simp [act, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, mul_comm]
  rw [aa_mul, aa_mul, aa_refl, aa_sub, aa_smul, hc, ← aa_mul,
    Matrix.mem_unitaryGroup_iff.mp hA, aa_one]

theorem solution {n : ℕ} (S R : Matrix (Qubits n) (Qubits n) ℂ)
    (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ)
    (hS : S ∈ Matrix.unitaryGroup (Qubits n) ℂ) (_hR : R ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hG : IsState psiG) (hB : IsState psiB) (horth : inner ℂ psiG psiB = 0)
    (_hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ Real.pi / 2)
    (hprep : act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB)
    (hRG : act R psiG = -psiG) (hRB : act R psiB = psiB) :
    let phiPlus := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG + Complex.I • psiB)
    let phiMinus := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG - Complex.I • psiB)
    IsState phiPlus ∧ IsState phiMinus ∧ inner ℂ phiPlus phiMinus = 0 ∧
      act (ampAmpIterate S R 0) phiPlus = Complex.exp (2 * Complex.I * θ) • phiPlus ∧
      act (ampAmpIterate S R 0) phiMinus = Complex.exp (-(2 * Complex.I * θ)) • phiMinus := by
  have huu : inner ℂ psiG psiG = 1 := inner_self_eq_one_of_norm_eq_one hG
  have hvv : inner ℂ psiB psiB = 1 := inner_self_eq_one_of_norm_eq_one hB
  have hvu : inner ℂ psiB psiG = 0 := by rw [← inner_conj_symm, horth, map_zero]
  have hw : act S (ket (0 : Qubits n)) =
      (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB := by
    have hz : (0 : Qubits n) = (fun _ => false) := by funext i; rfl
    simpa only [hz, zeroKet] using hprep
  have trig : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  have hGU : act (ampAmpIterate S R 0) psiG =
      (Real.cos (2 * θ) : ℂ) • psiG - (Real.sin (2 * θ) : ℂ) • psiB := by
    rw [ampAmpIterate, aa_mul, hRG, aa_reflect S hS, hw]
    simp only [inner_add_left, inner_smul_left, inner_neg_right, huu, hvu,
      Complex.conj_ofReal, mul_one, mul_zero, add_zero]
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.neg_apply, Real.sin_two_mul, Real.cos_two_mul,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    linear_combination -2 * psiG i * trig
  have hGV : act (ampAmpIterate S R 0) psiB =
      (Real.sin (2 * θ) : ℂ) • psiG + (Real.cos (2 * θ) : ℂ) • psiB := by
    rw [ampAmpIterate, aa_mul, hRB, aa_reflect S hS, hw]
    simp only [inner_add_left, inner_smul_left, hvv, horth,
      Complex.conj_ofReal, mul_one, mul_zero, zero_add]
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Real.sin_two_mul, Real.cos_two_mul,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  have hroot : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hscale : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * 2 = 1 := by
    field_simp [hr0]
    exact hroot.symm
  have hstate (v : EuclideanSpace ℂ (Qubits n)) (hv : inner ℂ v v = 1) : IsState v := by
    unfold IsState
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hv]
    norm_num
  dsimp only
  refine ⟨hstate _ ?_, hstate _ ?_, ?_, ?_, ?_⟩
  · simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      huu, hvv, horth, hvu, map_inv₀, Complex.conj_ofReal,
      Complex.conj_I, mul_zero, add_zero, zero_add, mul_one]
    linear_combination hscale - ((Real.sqrt 2)⁻¹ : ℂ)^2 * Complex.I_sq
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      huu, hvv, horth, hvu, map_inv₀, Complex.conj_ofReal,
      Complex.conj_I, mul_zero, sub_zero, zero_sub, mul_one]
    linear_combination hscale - ((Real.sqrt 2)⁻¹ : ℂ)^2 * Complex.I_sq
  · simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
      huu, hvv, horth, hvu, map_inv₀, Complex.conj_ofReal,
      Complex.conj_I, mul_zero, mul_one, add_zero, zero_add]
    linear_combination ((Real.sqrt 2)⁻¹ : ℂ)^2 * Complex.I_sq
  · have he : Complex.exp (2 * Complex.I * θ) =
        (Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * Complex.I := by
      rw [show (2 * Complex.I * θ : ℂ) = (2 * θ : ℝ) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I _
    rw [aa_smul, aa_add, aa_smul, hGU, hGV, he]
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination -((Real.sqrt 2)⁻¹ : ℂ) * (Real.sin (2 * θ) : ℂ) * psiB i * Complex.I_sq
  · have he : Complex.exp (-(2 * Complex.I * θ)) =
        (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * Complex.I := by
      rw [show (-(2 * Complex.I * θ) : ℂ) = (-(2 * θ) : ℝ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [aa_smul, aa_sub, aa_smul, hGU, hGV, he]
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination -((Real.sqrt 2)⁻¹ : ℂ) * (Real.sin (2 * θ) : ℂ) * psiB i * Complex.I_sq
