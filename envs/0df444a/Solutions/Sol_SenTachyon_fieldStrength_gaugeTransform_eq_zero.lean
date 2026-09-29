-- Prove2me | solution 1 for SenTachyon.fieldStrength_gaugeTransform_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:39:07.708984+00:00
-- url     : https://prove2.me/submissions/d12f7d04-52ab-4ac6-862b-a1fa4ef772a9

import Mathlib
import Definitions.Def_SenTachyon_Defs

set_option autoImplicit false

open scoped ContDiff

open SenTachyon in
theorem fsg_pd_mul {f g : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ}
    (hf : ∀ i j, DifferentiableAt ℝ (fun y => f y i j) x)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (μ : Fin 2) :
    partialDeriv μ (fun y => f y * g y) x = partialDeriv μ f x * g x + f x * partialDeriv μ g x := by
  ext i j
  simp only [partialDeriv, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]
  rw [(((hf i 0).hasFDerivAt.fun_mul (hg 0 j).hasFDerivAt).fun_add
    ((hf i 1).hasFDerivAt.fun_mul (hg 1 j).hasFDerivAt)).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem fsg_md_mul {f g : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ}
    (hf : ∀ i j, DifferentiableAt ℝ (fun y => f y i j) x)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    ∀ i j, DifferentiableAt ℝ (fun y => (f y * g y) i j) x := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))

open SenTachyon in
theorem fsg_pd_sub {f g : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ}
    (hf : ∀ i j, DifferentiableAt ℝ (fun y => f y i j) x)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (μ : Fin 2) :
    partialDeriv μ (fun y => f y - g y) x = partialDeriv μ f x - partialDeriv μ g x := by
  ext i j
  simp only [partialDeriv, Matrix.of_apply, Matrix.sub_apply]
  rw [((hf i j).hasFDerivAt.fun_sub (hg i j).hasFDerivAt).fderiv]
  simp only [_root_.sub_apply]

theorem fsg_md_sub {f g : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ}
    (hf : ∀ i j, DifferentiableAt ℝ (fun y => f y i j) x)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    ∀ i j, DifferentiableAt ℝ (fun y => (f y - g y) i j) x := by
  intro i j
  simp only [Matrix.sub_apply]
  exact (hf i j).sub (hg i j)

open SenTachyon in
theorem fsg_pd_smul {f : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ} (c : ℂ)
    (hf : ∀ i j, DifferentiableAt ℝ (fun y => f y i j) x) (μ : Fin 2) :
    partialDeriv μ (fun y => c • f y) x = c • partialDeriv μ f x := by
  ext i j
  simp only [partialDeriv, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [((hf i j).hasFDerivAt.const_mul c).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]

theorem fsg_md_smul {f : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ} (c : ℂ)
    (hf : ∀ i j, DifferentiableAt ℝ (fun y => f y i j) x) :
    ∀ i j, DifferentiableAt ℝ (fun y => (c • f y) i j) x := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hf i j).const_mul c

open SenTachyon in
theorem fsg_pd_const (C : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ × ℝ) (μ : Fin 2) :
    partialDeriv μ (fun _ => C) x = 0 := by
  ext i j
  simp [partialDeriv]

theorem fsg_inv_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M⁻¹ = (M 0 0 * M 1 1 - M 0 1 * M 1 0)⁻¹ • !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two, Matrix.det_fin_two]

theorem fsg_md_inv {Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ}
    (hΩ : ∀ i j, DifferentiableAt ℝ (fun y => Ω y i j) x) (hdet : IsUnit (Ω x).det) :
    ∀ i j, DifferentiableAt ℝ (fun y => (Ω y)⁻¹ i j) x := by
  have hd : DifferentiableAt ℝ
      (fun y => Ω y 0 0 * Ω y 1 1 - Ω y 0 1 * Ω y 1 0) x :=
    ((hΩ 0 0).mul (hΩ 1 1)).sub ((hΩ 0 1).mul (hΩ 1 0))
  have hne : Ω x 0 0 * Ω x 1 1 - Ω x 0 1 * Ω x 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]; exact hdet.ne_zero
  have hinv : DifferentiableAt ℝ
      (fun y => (Ω y 0 0 * Ω y 1 1 - Ω y 0 1 * Ω y 1 0)⁻¹) x := hd.inv hne
  intro i j
  simp only [fsg_inv_eq, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simpa using hinv.fun_mul (hΩ 1 1)
  · simpa using hinv.fun_mul (hΩ 0 1).fun_neg
  · simpa using hinv.fun_mul (hΩ 1 0).fun_neg
  · simpa using hinv.fun_mul (hΩ 0 0)

open SenTachyon in
theorem fsg_pd_inv {Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ × ℝ}
    (hΩ : ∀ i j, DifferentiableAt ℝ (fun y => Ω y i j) x) (hdet : ∀ y, IsUnit (Ω y).det)
    (μ : Fin 2) :
    partialDeriv μ (fun y => (Ω y)⁻¹) x = -((Ω x)⁻¹ * partialDeriv μ Ω x * (Ω x)⁻¹) := by
  have hP := fsg_md_inv hΩ (hdet x)
  have h := fsg_pd_mul hΩ hP μ
  have hone : (fun y => Ω y * (Ω y)⁻¹) = fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y; exact Matrix.mul_nonsing_inv _ (hdet y)
  rw [hone, fsg_pd_const] at h
  have hPW : (Ω x)⁻¹ * Ω x = 1 := Matrix.nonsing_inv_mul _ (hdet x)
  have h2 : Ω x * partialDeriv μ (fun y => (Ω y)⁻¹) x = -(partialDeriv μ Ω x * (Ω x)⁻¹) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
  calc partialDeriv μ (fun y => (Ω y)⁻¹) x
      = ((Ω x)⁻¹ * Ω x) * partialDeriv μ (fun y => (Ω y)⁻¹) x := by rw [hPW, one_mul]
    _ = (Ω x)⁻¹ * (Ω x * partialDeriv μ (fun y => (Ω y)⁻¹) x) := by rw [mul_assoc]
    _ = -((Ω x)⁻¹ * partialDeriv μ Ω x * (Ω x)⁻¹) := by rw [h2, mul_neg, mul_assoc]

open SenTachyon in
theorem fsg_md_pd {Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hΩ : ∀ i j, ContDiff ℝ 2 (fun x => Ω x i j)) (μ : Fin 2) (x : ℝ × ℝ) :
    ∀ i j, DifferentiableAt ℝ (fun y => partialDeriv μ Ω y i j) x := by
  intro i j
  simp only [partialDeriv, Matrix.of_apply]
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fun y => Ω y i j)) :=
    (hΩ i j).fderiv_right (by norm_num)
  exact (h1.clm_apply contDiff_const).differentiable (by simp) x

open SenTachyon in
theorem fsg_pd_symm {Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hΩ : ∀ i j, ContDiff ℝ 2 (fun x => Ω x i j)) (x : ℝ × ℝ) :
    partialDeriv 1 (partialDeriv 0 Ω) x = partialDeriv 0 (partialDeriv 1 Ω) x := by
  ext i j
  simp only [partialDeriv, Matrix.of_apply]
  have hsymm : IsSymmSndFDerivAt ℝ (fun y => Ω y i j) x :=
    (hΩ i j).contDiffAt.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => Ω y i j)) x :=
    (((hΩ i j).fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) x
  have key : ∀ v w : ℝ × ℝ, fderiv ℝ (fun y => fderiv ℝ (fun z => Ω z i j) y v) x w
      = fderiv ℝ (fderiv ℝ (fun z => Ω z i j)) x w v := by
    intro v w
    rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
    simp
  rw [key, key]
  exact hsymm _ _

theorem fsg_alg (W P A0 A1 a01 a10 D0 D1 E : Matrix (Fin 2) (Fin 2) ℂ) (hPW : P * W = 1) :
    ((D0 * A1 + W * a01) * P + W * A1 * (-(P * D0 * P))
        - Complex.I • (E * P + D1 * (-(P * D0 * P))))
      - ((D1 * A0 + W * a10) * P + W * A0 * (-(P * D1 * P))
        - Complex.I • (E * P + D0 * (-(P * D1 * P))))
      - Complex.I • ((W * A0 * P - Complex.I • (D0 * P)) * (W * A1 * P - Complex.I • (D1 * P))
        - (W * A1 * P - Complex.I • (D1 * P)) * (W * A0 * P - Complex.I • (D0 * P)))
      = W * (a01 - a10 - Complex.I • (A0 * A1 - A1 * A0)) * P := by
  have hPW' : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, P * (W * X) = X := by
    intro X; rw [← mul_assoc, hPW, one_mul]
  simp only [mul_sub, sub_mul, add_mul, mul_neg, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_add, smul_neg, smul_smul, mul_assoc, hPW', Complex.I_mul_I,
    neg_smul, one_smul]
  abel

open SenTachyon in
theorem fsg_pd_gauge {Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ} {A : GaugeField}
    (hΩ : ∀ i j, ContDiff ℝ 2 (fun x => Ω x i j))
    (hA : ∀ μ i j, ContDiff ℝ 1 (fun x => A μ x i j))
    (hdet : ∀ x, IsUnit (Ω x).det) (x : ℝ × ℝ) (μ ν : Fin 2) :
    partialDeriv μ (gaugeTransform Ω A ν) x
      = (partialDeriv μ Ω x * A ν x + Ω x * partialDeriv μ (A ν) x) * (Ω x)⁻¹
          + Ω x * A ν x * (-((Ω x)⁻¹ * partialDeriv μ Ω x * (Ω x)⁻¹))
        - Complex.I • (partialDeriv μ (partialDeriv ν Ω) x * (Ω x)⁻¹
          + partialDeriv ν Ω x * (-((Ω x)⁻¹ * partialDeriv μ Ω x * (Ω x)⁻¹))) := by
  have dΩ : ∀ i j, DifferentiableAt ℝ (fun y => Ω y i j) x := fun i j =>
    ((hΩ i j).differentiable (by simp)) x
  have dA : ∀ i j, DifferentiableAt ℝ (fun y => A ν y i j) x := fun i j =>
    ((hA ν i j).differentiable (by simp)) x
  have dP := fsg_md_inv dΩ (hdet x)
  have dD := fsg_md_pd hΩ ν x
  have e1 : partialDeriv μ (fun y => Ω y * A ν y) x
      = partialDeriv μ Ω x * A ν x + Ω x * partialDeriv μ (A ν) x := fsg_pd_mul dΩ dA μ
  have e2 : partialDeriv μ (fun y => Ω y * A ν y * (Ω y)⁻¹) x
      = partialDeriv μ (fun y => Ω y * A ν y) x * (Ω x)⁻¹
        + Ω x * A ν x * partialDeriv μ (fun y => (Ω y)⁻¹) x :=
    fsg_pd_mul (fsg_md_mul dΩ dA) dP μ
  have e3 : partialDeriv μ (fun y => partialDeriv ν Ω y * (Ω y)⁻¹) x
      = partialDeriv μ (partialDeriv ν Ω) x * (Ω x)⁻¹
        + partialDeriv ν Ω x * partialDeriv μ (fun y => (Ω y)⁻¹) x :=
    fsg_pd_mul dD dP μ
  have e4 : partialDeriv μ (fun y => Complex.I • (partialDeriv ν Ω y * (Ω y)⁻¹)) x
      = Complex.I • partialDeriv μ (fun y => partialDeriv ν Ω y * (Ω y)⁻¹) x :=
    fsg_pd_smul Complex.I (fsg_md_mul dD dP) μ
  have e5 : partialDeriv μ (gaugeTransform Ω A ν) x
      = partialDeriv μ (fun y => Ω y * A ν y * (Ω y)⁻¹) x
        - partialDeriv μ (fun y => Complex.I • (partialDeriv ν Ω y * (Ω y)⁻¹)) x :=
    fsg_pd_sub (fsg_md_mul (fsg_md_mul dΩ dA) dP)
      (fsg_md_smul Complex.I (fsg_md_mul dD dP)) μ
  rw [e5, e4, e3, e2, e1, fsg_pd_inv dΩ hdet μ]

open SenTachyon in
theorem solution (Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (A : GaugeField)
    (hΩ : ∀ i j, ContDiff ℝ 2 (fun x => Ω x i j))
    (hA : ∀ μ i j, ContDiff ℝ 1 (fun x => A μ x i j))
    (hdet : ∀ x, IsUnit (Ω x).det)
    (hF : ∀ x, fieldStrength A x = 0) :
    ∀ x, fieldStrength (gaugeTransform Ω A) x = 0 := by
  intro x
  have key : fieldStrength (gaugeTransform Ω A) x = Ω x * fieldStrength A x * (Ω x)⁻¹ := by
    have h01 := fsg_pd_gauge hΩ hA hdet x 0 1
    have h10 := fsg_pd_gauge hΩ hA hdet x 1 0
    rw [fsg_pd_symm hΩ x] at h10
    have g0 : gaugeTransform Ω A 0 x
        = Ω x * A 0 x * (Ω x)⁻¹ - Complex.I • (partialDeriv 0 Ω x * (Ω x)⁻¹) := rfl
    have g1 : gaugeTransform Ω A 1 x
        = Ω x * A 1 x * (Ω x)⁻¹ - Complex.I • (partialDeriv 1 Ω x * (Ω x)⁻¹) := rfl
    have hF' : fieldStrength A x = partialDeriv 0 (A 1) x - partialDeriv 1 (A 0) x
        - Complex.I • (A 0 x * A 1 x - A 1 x * A 0 x) := rfl
    have hG : fieldStrength (gaugeTransform Ω A) x
        = partialDeriv 0 (gaugeTransform Ω A 1) x - partialDeriv 1 (gaugeTransform Ω A 0) x
          - Complex.I • (gaugeTransform Ω A 0 x * gaugeTransform Ω A 1 x
            - gaugeTransform Ω A 1 x * gaugeTransform Ω A 0 x) := rfl
    rw [hG, h01, h10, g0, g1, hF']
    exact fsg_alg (Ω x) (Ω x)⁻¹ (A 0 x) (A 1 x) (partialDeriv 0 (A 1) x)
      (partialDeriv 1 (A 0) x) (partialDeriv 0 Ω x) (partialDeriv 1 Ω x)
      (partialDeriv 0 (partialDeriv 1 Ω) x) (Matrix.nonsing_inv_mul _ (hdet x))
  rw [key, hF x, mul_zero, zero_mul]
