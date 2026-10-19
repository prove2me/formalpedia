-- Prove2me | solution 1 for QAlgorithms.pgmSuccess_uniform_real_gram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:17:20.768186+00:00
-- url     : https://prove2.me/submissions/da31fcb5-3fa4-450b-943f-c7f951751c9b

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix QAlgorithms

private noncomputable def complexify {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ where
  toFun A := A.map Complex.ofReal
  map_zero' := by ext i j; simp
  map_one' := by ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
  map_add' A B := by ext i j; simp
  map_mul' A B := by ext i j; simp [Matrix.mul_apply, Complex.ofReal_sum]
  commutes' r := by ext i j; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]; split_ifs <;> simp
  map_star' A := by ext i j; simp [star_eq_conjTranspose]

private lemma gram_sandwich {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (V : Matrix m n ℂ) :
    Vᴴ * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (V * Vᴴ) * V =
      cfc Real.sqrt (Vᴴ * V) := by
  let A := V * Vᴴ
  let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A
  have hA : A.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hS : S.PosSemidef := (cfc_nonneg (a := A) (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg x))).posSemidef
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hSA : (S * A * S - 1) * A = 0 := by
    have heq : (S * A * S - 1) * A =
        cfc (fun x : ℝ => ((Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ - 1) * x) A := by
      rw [cfc_mul _ _ A (hcont _) (hcont _), cfc_sub _ _ A (hcont _) (hcont _),
        cfc_mul _ _ A (hcont _) (hcont _), cfc_mul _ _ A (hcont _) (hcont _)]
      simp only [cfc_id', cfc_const_one, hA.isHermitian.isSelfAdjoint]
      rfl
    rw [heq, ← cfc_const_zero ℝ A]
    apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hA.nonneg hx
    by_cases h : x = 0
    · simp [h]
    · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hx0 (Ne.symm h))).ne'
      have hs2 := Real.sq_sqrt hx0
      field_simp
      nlinarith
  have hSV : (S * A * S - 1) * V = 0 :=
    (Matrix.mul_self_mul_conjTranspose_eq_zero V _).mp hSA
  have hsupport : S * A * S * V = V := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using hSV
  have hB : (Vᴴ * S * V).PosSemidef := hS.conjTranspose_mul_mul_same V
  have hsq : (Vᴴ * S * V) * (Vᴴ * S * V) = Vᴴ * V := by
    calc
      _ = Vᴴ * (S * A * S * V) := by simp only [A, Matrix.mul_assoc]
      _ = _ := by rw [hsupport]
  have hC : (cfc Real.sqrt (Vᴴ * V)).PosSemidef :=
    (cfc_nonneg (a := Vᴴ * V) (fun x _ => Real.sqrt_nonneg x)).posSemidef
  have hsqC : cfc Real.sqrt (Vᴴ * V) * cfc Real.sqrt (Vᴴ * V) = Vᴴ * V := by
    rw [← cfc_mul Real.sqrt Real.sqrt (Vᴴ * V)]
    calc
      _ = cfc (id : ℝ → ℝ) (Vᴴ * V) := cfc_congr (fun x hx =>
        Real.mul_self_sqrt (spectrum_nonneg_of_nonneg
          (Matrix.posSemidef_conjTranspose_mul_self V).nonneg hx))
      _ = _ := cfc_id ℝ _ (Matrix.posSemidef_conjTranspose_mul_self V).isHermitian
  exact (CFC.mul_self_eq_mul_self_iff _ _ hB.nonneg hC.nonneg).mp (hsq.trans hsqC.symm)

private lemma sqrt_scale {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : ℝ) (hp : 0 ≤ p) :
    cfc Real.sqrt (p • A) = Real.sqrt p • cfc Real.sqrt A := by
  calc
    _ = cfc (fun x : ℝ => Real.sqrt (p * x)) A :=
      (cfc_comp_const_mul p Real.sqrt A (ha := hA)).symm
    _ = cfc (fun x : ℝ => Real.sqrt p * Real.sqrt x) A :=
      cfc_congr (fun x _ => Real.sqrt_mul hp x)
    _ = _ := cfc_const_mul (Real.sqrt p) Real.sqrt A

private def cols {O ι : Type*} (ψ : O → EuclideanSpace ℂ ι) : Matrix ι O ℂ :=
  fun a i => ψ i a

private lemma cols_gram {O ι : Type*} [Fintype ι]
    (ψ : O → EuclideanSpace ℂ ι) (i j : O) :
    ((cols ψ)ᴴ * cols ψ) i j = inner ℂ (ψ i) (ψ j) := by
  simp [cols, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

private lemma cols_density {O ι : Type*} [Fintype O]
    (ψ : O → EuclideanSpace ℂ ι) :
    cols ψ * (cols ψ)ᴴ = ∑ i, pureDensity (ψ i) := by
  ext a b
  simp [cols, Matrix.mul_apply, pureDensity, Matrix.sum_apply]

private lemma cols_sandwich {O ι : Type*} [Fintype O] [Fintype ι]
    (ψ : O → EuclideanSpace ℂ ι) (S : Matrix ι ι ℂ) (i : O) :
    ((cols ψ)ᴴ * S * cols ψ) i i = inner ℂ (ψ i) (act S (ψ i)) := by
  simp only [Matrix.mul_assoc]
  simp [Matrix.mul_apply, cols, act, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Matrix.mulVec, mul_comm]

theorem solution {O ι : Type*}
    [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]
    (ψ : O → EuclideanSpace ℂ ι) (G : Matrix O O ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j) = (G i j : ℂ)) :
    QAlgorithms.pgmSuccess (fun _ : O => (Fintype.card O : ℝ)⁻¹) ψ =
      (Fintype.card O : ℝ)⁻¹ * ∑ i, (QAlgorithms.psdSqrt G i i)^2 := by
  classical
  cases isEmpty_or_nonempty O with
  | inl h => simp [pgmSuccess]
  | inr h =>
    let p : ℝ := (Fintype.card O : ℝ)⁻¹
    have hp : 0 < p := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    let c : ℝ := Real.sqrt p
    have hc : c ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    let χ : O → EuclideanSpace ℂ ι := fun i => (c : ℂ) • ψ i
    let ρ : Matrix ι ι ℂ := ∑ i, pureDensity (χ i)
    let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ
    have hGH : G.IsHermitian := by
      ext i j
      apply Complex.ofReal_injective
      simpa [Matrix.conjTranspose_apply, hG] using inner_conj_symm (𝕜 := ℂ) (ψ i) (ψ j)
    have hW : (cols χ)ᴴ * cols χ = complexify (p • G) := by
      ext i j
      rw [cols_gram]
      simp only [χ, inner_smul_left, inner_smul_right, hG,
        Complex.conj_ofReal]
      change (c : ℂ) * ((c : ℂ) * (G i j : ℂ)) = ((p * G i j : ℝ) : ℂ)
      rw [← mul_assoc, ← Complex.ofReal_mul, show c * c = p from Real.mul_self_sqrt hp.le]
      simp
    have hmap : complexify (cfc Real.sqrt (p • G)) =
        cfc Real.sqrt (complexify (p • G)) := by
      have hφ : Continuous (complexify : Matrix O O ℝ → Matrix O O ℂ) := by
        change Continuous (fun A : Matrix O O ℝ => A.map Complex.ofReal)
        exact continuous_pi fun i => continuous_pi fun j =>
          Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))
      exact StarAlgHom.map_cfc complexify Real.sqrt (p • G) (by fun_prop) hφ
        (hGH.smul (isSelfAdjoint_iff.mpr (by simp : star p = p))).isSelfAdjoint (by
          rw [← hW]
          exact (Matrix.posSemidef_conjTranspose_mul_self (cols χ)).isHermitian)
    have hid : (cols χ)ᴴ * S * cols χ = complexify (c • psdSqrt G) := by
      change (cols χ)ᴴ * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ * cols χ = _
      change (cols χ)ᴴ * cfc (fun x : ℝ => (Real.sqrt x)⁻¹)
        (∑ i, pureDensity (χ i)) * cols χ = _
      rw [← cols_density χ, gram_sandwich, hW, ← hmap,
        sqrt_scale G hGH p hp.le]
      rfl
    have hdiag (i : O) : inner ℂ (ψ i) (act S (χ i)) = (psdSqrt G i i : ℂ) := by
      have hi := congrArg (fun A : Matrix O O ℂ => A i i) hid
      rw [cols_sandwich] at hi
      change inner ℂ ((c : ℂ) • ψ i) (act S (χ i)) = ((c * psdSqrt G i i : ℝ) : ℂ) at hi
      simp only [inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul] at hi
      exact mul_left_cancel₀ hcC hi
    unfold pgmSuccess
    change (∑ i, p * ‖inner ℂ (act S (χ i)) (ψ i)‖ ^ 2) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [← inner_conj_symm, hdiag]
    simp [Complex.norm_real, sq_abs]
