-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P20.left_tight_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:34:45.588454+00:00
-- url     : https://prove2.me/submissions/b3206519-6381-48c8-bb8f-c44fce3e2231

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P20
noncomputable section

open MeasureTheory

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P40 (operatorKet)

open QAlgorithms.Papers.Independent.Renew46.P20
open QAlgorithms

def g65b_Phi {I : Type*} [Fintype I] (X : Matrix I I ℂ) :
    Matrix (I × I) (I × I) ℂ →L[ℂ] Matrix I I ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.of fun o o' => ∑ i, ∑ i', M (o, i) (o', i') * X i i'
      map_add' := by intro A B; ext; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro r A; ext; simp [Finset.mul_sum, mul_assoc] }

def g65b_Psi (I : Type*) [Fintype I] :
    Matrix (I × I) (I × I) ℂ →L[ℂ] Matrix (I × I) (I × I) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.of fun p q => M (p.1, q.1) (p.2, q.2)
      map_add' := by intro A B; ext; simp
      map_smul' := by intro r A; ext; simp }

theorem g65b_Phi_apply {I : Type*} [Fintype I] (X A : Matrix I I ℂ) :
    g65b_Phi X (pureDensity (operatorKet A)) = A * X * Aᴴ := by
  ext o o'
  simp only [g65b_Phi, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.of_apply, pureDensity, operatorKet, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp [Complex.star_def]; ring

theorem g65b_Psi_apply {I : Type*} [Fintype I] (A : Matrix I I ℂ) :
    g65b_Psi I (pureDensity (operatorKet A)) =
      Matrix.kronecker A (fun i j => conj (A i j)) := by
  ext p q
  simp [g65b_Psi, pureDensity, operatorKet, Matrix.kronecker]; rfl

/-- PDF p.17, Definition 4 and both identities in Eq.(85).
A finite measure and an integrable measurable frame are used; K may be singular
or zero, and the measure need not be a probability measure. -/
theorem solution
    {I W : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace W]
    (mu : Measure W) [IsFiniteMeasure mu] (A : W → Matrix I I ℂ)
    (hA : StronglyMeasurable A)
    (hframe : Integrable (fun w => pureDensity (operatorKet (A w))) mu)
    (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (frameOperator mu A = Matrix.kronecker (1 : Matrix I I ℂ) K ↔
      ∀ X : Matrix I I ℂ,
        Integrable (fun w => A w * X * (A w)ᴴ) mu ∧
        (∫ w, A w * X * (A w)ᴴ ∂mu) =
          (X * K.transpose).trace • (1 : Matrix I I ℂ)) ∧
    (frameOperator mu A = Matrix.kronecker (1 : Matrix I I ℂ) K ↔
      Integrable (fun w => Matrix.kronecker (A w)
        (fun i j => conj (A w i j))) mu ∧
      (∫ w, Matrix.kronecker (A w) (fun i j => conj (A w i j)) ∂mu) =
        (fun p q => operatorKet (1 : Matrix I I ℂ) p *
          conj (operatorKet K.transpose q))) := by
  have e1 : ∀ X : Matrix I I ℂ, (fun w => A w * X * (A w)ᴴ) =
      fun w => g65b_Phi X (pureDensity (operatorKet (A w))) := by
    intro X; funext w; rw [g65b_Phi_apply]
  have i1 : ∀ X : Matrix I I ℂ, Integrable (fun w => A w * X * (A w)ᴴ) mu := by
    intro X; rw [e1]; exact (g65b_Phi X).integrable_comp hframe
  have j1 : ∀ X : Matrix I I ℂ, (∫ w, A w * X * (A w)ᴴ ∂mu) = g65b_Phi X (frameOperator mu A) := by
    intro X; rw [e1]; exact (g65b_Phi X).integral_comp_comm hframe
  have e2 : (fun w => Matrix.kronecker (A w) (fun i j => conj (A w i j))) =
      fun w => g65b_Psi I (pureDensity (operatorKet (A w))) := by
    funext w; rw [g65b_Psi_apply]
  have i2 : Integrable (fun w => Matrix.kronecker (A w) (fun i j => conj (A w i j))) mu := by
    rw [e2]; exact (g65b_Psi I).integrable_comp hframe
  have j2 : (∫ w, Matrix.kronecker (A w) (fun i j => conj (A w i j)) ∂mu) =
      g65b_Psi I (frameOperator mu A) := by
    rw [e2]; exact (g65b_Psi I).integral_comp_comm hframe
  have hKh : ∀ i j, conj (K j i) = K i j := by
    intro i j
    have := congrFun (congrFun hK.isHermitian.eq i) j
    simpa [Matrix.conjTranspose_apply] using this
  refine ⟨⟨fun hF X => ⟨i1 X, ?_⟩, fun h => ?_⟩, ⟨fun hF => ⟨i2, ?_⟩, fun h => ?_⟩⟩
  · rw [j1, hF]
    ext o o'
    simp only [g65b_Phi, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
      smul_eq_mul]
    by_cases ho : o = o'
    · simp only [ho, if_true, one_mul, mul_one]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
    · simp [ho]
  · ext ⟨o, i⟩ ⟨o', i'⟩
    have := congrFun (congrFun (h (Matrix.single i i' 1)).2 o) o'
    rw [j1] at this
    simp only [g65b_Phi, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
      smul_eq_mul, Matrix.single_apply] at this
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simpa [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm] using this
  · rw [j2, hF]
    ext ⟨o, o'⟩ ⟨i, i'⟩
    simp [g65b_Psi, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, operatorKet, hKh]
  · ext ⟨o, i⟩ ⟨o', i'⟩
    have := congrFun (congrFun h.2 (o, o')) (i, i')
    rw [j2] at this
    simpa [g65b_Psi, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, operatorKet, hKh] using this



end
