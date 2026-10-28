-- Prove2me | solution 1 for SimpleSSA.Monotone.petz_map_properties
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:11:40.052824+00:00
-- url     : https://prove2.me/submissions/22b12bf0-6c0f-4a75-bfbb-eca82ab257c0

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

noncomputable section

namespace SimpleSSA.Monotone.PetzProof

open WildeQIT

variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

omit [DecidableEq A] in
lemma hsInner_eq_sum (X Y : Matrix A A ℂ) :
    hsInner X Y = ∑ i, ∑ j, star (X i j) * Y i j := by
  simp only [hsInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

omit [DecidableEq A] in
lemma hsInner_applyHS (X : Matrix A A ℂ) (M : Matrix (A × A) (A × A) ℂ) :
    hsInner X (applyHS M X) = star (vecHS X) ⬝ᵥ (M *ᵥ vecHS X) := by
  rw [hsInner_eq_sum]
  simp [dotProduct, Fintype.sum_prod_type, vecHS, applyHS]

lemma hsInner_single_right (X : Matrix A A ℂ) (i j : A) :
    hsInner X (Matrix.single i j 1) = star (X i j) := by
  simp [hsInner, Matrix.trace_mul_single]

omit [Fintype A] [DecidableEq A] in
lemma vecHS_surjective : Function.Surjective (vecHS (A := A)) := by
  intro v
  exact ⟨Matrix.of (fun i j => v (i, j)), rfl⟩

omit [Fintype C] [DecidableEq C] in
lemma linear_matrix_mulVec (F : Matrix A A ℂ →ₗ[ℂ] Matrix C C ℂ) (X : Matrix A A ℂ) :
    (Matrix.of fun p q => F (Matrix.single q.1 q.2 1) p.1 p.2) *ᵥ vecHS X = vecHS (F X) := by
  ext p
  change (∑ q : A × A, F (Matrix.single q.1 q.2 1) p.1 p.2 * X q.1 q.2) = F X p.1 p.2
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by simp,
    map_smul]
  simp [mul_comm]

omit [DecidableEq A] in
lemma kronecker_mulVec_vecHS (L R X : Matrix A A ℂ) :
    (L ⊗ₖ Rᵀ) *ᵥ vecHS X = vecHS (L * X * R) := by
  rw [Matrix.mul_assoc]
  ext p
  simp [Matrix.mulVec, dotProduct, vecHS, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.mul_sum, mul_left_comm, mul_comm]

lemma modularOp_mulVec (ρ σ X : Matrix A A ℂ) :
    modularOp ρ σ *ᵥ vecHS X = vecHS (σ * X * ρ⁻¹) :=
  kronecker_mulVec_vecHS σ ρ⁻¹ X

def petzLinear (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun := petzMap ρ
  map_add' X Y := by simp [petzMap, Matrix.add_mul, Matrix.add_kronecker]
  map_smul' c X := by simp [petzMap, Matrix.smul_kronecker]

lemma petzMatrix_mulVec (ρ : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    petzMatrix ρ *ᵥ vecHS X = vecHS (petzMap ρ X) :=
  linear_matrix_mulVec (petzLinear ρ) X

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma partialTrace_conjTranspose (Y : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight Yᴴ = (partialTraceRight Y)ᴴ := by
  ext i j
  simp [partialTraceRight, Matrix.conjTranspose_apply]

omit [DecidableEq A] [DecidableEq B] in
lemma trace_partialTrace (Y : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceRight Y) = Matrix.trace Y := by
  simp [partialTraceRight, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

omit [DecidableEq A] in
lemma partialTrace_mul_kronecker (Y : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    partialTraceRight (Y * (X ⊗ₖ (1 : Matrix B B ℂ))) = partialTraceRight Y * X := by
  ext i j
  simp [partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Matrix.one_apply]
  exact Finset.sum_comm

omit [DecidableEq A] in
lemma partialTrace_kronecker_mul (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight ((X ⊗ₖ (1 : Matrix B B ℂ)) * Y) = X * partialTraceRight Y := by
  ext i j
  simp [partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum,
    Matrix.one_apply]
  exact Finset.sum_comm

omit [DecidableEq A] in
lemma hsInner_partialTrace (Y : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    hsInner (partialTraceRight Y) X = hsInner Y (X ⊗ₖ (1 : Matrix B B ℂ)) := by
  unfold hsInner
  rw [← partialTrace_conjTranspose, ← partialTrace_mul_kronecker, trace_partialTrace]

end SimpleSSA.Monotone.PetzProof

namespace SimpleSSA.Monotone.PetzProof

open WildeQIT

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
lemma hsInner_mul_right (X Y Z : Matrix A A ℂ) :
    hsInner (X * Y) Z = hsInner X (Z * Yᴴ) := by
  unfold hsInner
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [Matrix.mul_assoc]

lemma petz_adjoint_identity (ρ : Matrix (A × B) (A × B) ℂ)
    (hS : (sqrtM ρ)ᴴ = sqrtM ρ)
    (hR : (invSqrtM (partialTraceRight ρ))ᴴ = invSqrtM (partialTraceRight ρ))
    (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    hsInner (petzAdjoint ρ Y) X = hsInner Y (petzMap ρ X) := by
  unfold petzAdjoint
  rw [hsInner_partialTrace, hsInner_mul_right, hsInner_mul_right,
    Matrix.conjTranspose_kronecker, hR, Matrix.conjTranspose_one, hS,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rfl

lemma petzMatrix_conjTranspose_mulVec (ρ : Matrix (A × B) (A × B) ℂ)
    (hAdj : ∀ (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ),
      hsInner (petzAdjoint ρ Y) X = hsInner Y (petzMap ρ X))
    (Y : Matrix (A × B) (A × B) ℂ) :
    (petzMatrix ρ)ᴴ *ᵥ vecHS Y = vecHS (petzAdjoint ρ Y) := by
  ext p
  have h := congrArg star (hAdj (Matrix.single p.1 p.2 1) Y)
  rw [hsInner_single_right, star_star, hsInner_eq_sum] at h
  simpa [Matrix.mulVec, dotProduct, petzMatrix, Matrix.conjTranspose_apply,
    vecHS, Fintype.sum_prod_type, mul_comm] using h.symm

lemma petz_adjoint_petz (ρ : Matrix (A × B) (A × B) ℂ)
    (hS : sqrtM ρ * sqrtM ρ = ρ)
    (hR : invSqrtM (partialTraceRight ρ) * partialTraceRight ρ *
      invSqrtM (partialTraceRight ρ) = 1) (X : Matrix A A ℂ) :
    petzAdjoint ρ (petzMap ρ X) = X := by
  unfold petzAdjoint petzMap
  rw [Matrix.mul_assoc _ (sqrtM ρ) (sqrtM ρ), hS,
    partialTrace_mul_kronecker, partialTrace_kronecker_mul]
  calc
    _ = X * (invSqrtM (partialTraceRight ρ) * partialTraceRight ρ *
        invSqrtM (partialTraceRight ρ)) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hR, Matrix.mul_one]

lemma petz_adjoint_modular_petz (ρ σ : Matrix (A × B) (A × B) ℂ)
    (hS : sqrtM ρ * ρ⁻¹ * sqrtM ρ = 1)
    (hR : invSqrtM (partialTraceRight ρ) * invSqrtM (partialTraceRight ρ) =
      (partialTraceRight ρ)⁻¹) (X : Matrix A A ℂ) :
    petzAdjoint ρ (σ * petzMap ρ X * ρ⁻¹) =
      partialTraceRight σ * X * (partialTraceRight ρ)⁻¹ := by
  unfold petzAdjoint petzMap
  have heq : σ * (((X * invSqrtM (partialTraceRight ρ)) ⊗ₖ (1 : Matrix B B ℂ)) *
      sqrtM ρ) * ρ⁻¹ * sqrtM ρ *
        (invSqrtM (partialTraceRight ρ) ⊗ₖ (1 : Matrix B B ℂ)) =
      σ * (((X * invSqrtM (partialTraceRight ρ)) ⊗ₖ (1 : Matrix B B ℂ)) *
        (invSqrtM (partialTraceRight ρ) ⊗ₖ (1 : Matrix B B ℂ))) := by
    calc
      _ = σ * (((X * invSqrtM (partialTraceRight ρ)) ⊗ₖ (1 : Matrix B B ℂ)) *
          (sqrtM ρ * ρ⁻¹ * sqrtM ρ) *
          (invSqrtM (partialTraceRight ρ) ⊗ₖ (1 : Matrix B B ℂ))) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS, Matrix.mul_one]
  rw [heq, ← Matrix.mul_kronecker_mul, Matrix.one_mul, partialTrace_mul_kronecker]
  simp only [Matrix.mul_assoc, hR]

lemma petz_map_sqrt (ρ : Matrix (A × B) (A × B) ℂ)
    (hR : sqrtM (partialTraceRight ρ) * invSqrtM (partialTraceRight ρ) = 1) :
    petzMap ρ (sqrtM (partialTraceRight ρ)) = sqrtM ρ := by
  rw [petzMap, hR, Matrix.one_kronecker_one, Matrix.one_mul]

lemma petz_isometry_matrix (ρ : Matrix (A × B) (A × B) ℂ)
    (hAdj : ∀ (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ),
      hsInner (petzAdjoint ρ Y) X = hsInner Y (petzMap ρ X))
    (hcomp : ∀ X : Matrix A A ℂ, petzAdjoint ρ (petzMap ρ X) = X) :
    (petzMatrix ρ)ᴴ * petzMatrix ρ = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨X, rfl⟩ := vecHS_surjective v
  rw [← Matrix.mulVec_mulVec, petzMatrix_mulVec,
    petzMatrix_conjTranspose_mulVec ρ hAdj, hcomp, Matrix.one_mulVec]

lemma petz_modular_matrix (ρ σ : Matrix (A × B) (A × B) ℂ)
    (hAdj : ∀ (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ),
      hsInner (petzAdjoint ρ Y) X = hsInner Y (petzMap ρ X))
    (hcomp : ∀ X : Matrix A A ℂ, petzAdjoint ρ (σ * petzMap ρ X * ρ⁻¹) =
      partialTraceRight σ * X * (partialTraceRight ρ)⁻¹) :
    (petzMatrix ρ)ᴴ * modularOp ρ σ * petzMatrix ρ =
      modularOp (partialTraceRight ρ) (partialTraceRight σ) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨X, rfl⟩ := vecHS_surjective v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, petzMatrix_mulVec,
    modularOp_mulVec, petzMatrix_conjTranspose_mulVec ρ hAdj, hcomp, modularOp_mulVec]

end SimpleSSA.Monotone.PetzProof

open scoped MatrixOrder

namespace SimpleSSA.Monotone.PositivityProof

open TroppMatrixConcentration QAlgorithms WildeQIT

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma partialTraceRight_eq_sum (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight ρ = ∑ b : B, ρ.submatrix (fun a => (a, b)) (fun a => (a, b)) := by
  ext i j
  simp [partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma partialTraceRight_posSemidef (ρ : Matrix (A × B) (A × B) ℂ)
    (hρ : ρ.PosSemidef) : (partialTraceRight ρ).PosSemidef := by
  rw [partialTraceRight_eq_sum]
  exact Matrix.posSemidef_sum Finset.univ (fun b _ => hρ.submatrix (fun a => (a, b)))

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma partialTraceRight_posDef [Nonempty B] (ρ : Matrix (A × B) (A × B) ℂ)
    (hρ : ρ.PosDef) : (partialTraceRight ρ).PosDef := by
  rw [partialTraceRight_eq_sum]
  exact Matrix.posDef_sum Finset.univ_nonempty (fun b _ =>
    hρ.submatrix (fun _ _ h => congrArg Prod.fst h))

end SimpleSSA.Monotone.PositivityProof

namespace SimpleSSA.Monotone.SpectralProof

variable {A : Type} [Fintype A] [DecidableEq A]
variable {M : Matrix A A ℂ}

lemma sqrtM_isHermitian (M : Matrix A A ℂ) : (sqrtM M).IsHermitian :=
  cfc_predicate Real.sqrt M

lemma invSqrtM_isHermitian (M : Matrix A A ℂ) : (invSqrtM M).IsHermitian :=
  cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹) M

lemma sqrtM_conjTranspose (M : Matrix A A ℂ) : (sqrtM M)ᴴ = sqrtM M :=
  sqrtM_isHermitian M

lemma invSqrtM_conjTranspose (M : Matrix A A ℂ) : (invSqrtM M)ᴴ = invSqrtM M :=
  invSqrtM_isHermitian M

lemma sqrtM_mul_self (hM : M.PosSemidef) : sqrtM M * sqrtM M = M := by
  change cfc Real.sqrt M * cfc Real.sqrt M = M
  rw [← cfc_mul Real.sqrt Real.sqrt M]
  calc
    cfc (fun x => Real.sqrt x * Real.sqrt x) M = cfc (fun x : ℝ => x) M :=
      cfc_congr (fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hM.nonneg hx))
    _ = M := cfc_id' ℝ M hM.isHermitian

lemma spectrum_pos (hM : M.PosDef) {x : ℝ} (hx : x ∈ spectrum ℝ M) : 0 < x :=
  hM.isStrictlyPositive.spectrum_pos hx

lemma sqrtM_mul_invSqrtM (hM : M.PosDef) : sqrtM M * invSqrtM M = 1 := by
  exact (cfcUnits Real.sqrt M
    (fun x hx => ne_of_gt (Real.sqrt_pos.2 (spectrum_pos hM hx)))
    (ha := hM.isHermitian)).val_inv

lemma invSqrtM_mul_sqrtM (hM : M.PosDef) : invSqrtM M * sqrtM M = 1 := by
  exact (cfcUnits Real.sqrt M
    (fun x hx => ne_of_gt (Real.sqrt_pos.2 (spectrum_pos hM hx)))
    (ha := hM.isHermitian)).inv_val

lemma sqrtM_inv (hM : M.PosDef) : (sqrtM M)⁻¹ = invSqrtM M :=
  Matrix.inv_eq_right_inv (sqrtM_mul_invSqrtM hM)

lemma invSqrtM_mul_self (hM : M.PosDef) : invSqrtM M * invSqrtM M = M⁻¹ := by
  rw [← sqrtM_inv hM, ← Matrix.mul_inv_rev, sqrtM_mul_self hM.posSemidef]

lemma invSqrtM_mul_self_mul_invSqrtM (hM : M.PosDef) :
    invSqrtM M * M * invSqrtM M = 1 := by
  calc
    invSqrtM M * M * invSqrtM M =
        invSqrtM M * (sqrtM M * sqrtM M) * invSqrtM M := by
      rw [sqrtM_mul_self hM.posSemidef]
    _ = (invSqrtM M * sqrtM M) * (sqrtM M * invSqrtM M) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [invSqrtM_mul_sqrtM hM, sqrtM_mul_invSqrtM hM, one_mul]

lemma sqrtM_mul_inv_mul_sqrtM (hM : M.PosDef) :
    sqrtM M * M⁻¹ * sqrtM M = 1 := by
  rw [← invSqrtM_mul_self hM, ← Matrix.mul_assoc, sqrtM_mul_invSqrtM hM,
    one_mul, invSqrtM_mul_sqrtM hM]

end SimpleSSA.Monotone.SpectralProof


open SimpleSSA.Monotone
open TroppMatrixConcentration QAlgorithms WildeQIT

theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ σ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef)
    (hσ : IsDensityMatrix σ) (hσ_inv : σ.PosDef) :
    (petzMatrix ρ)ᴴ * modularOp ρ σ * petzMatrix ρ =
        modularOp (partialTraceRight ρ) (partialTraceRight σ) ∧
      petzMap ρ (sqrtM (partialTraceRight ρ)) = sqrtM ρ ∧
      (petzMatrix ρ)ᴴ * petzMatrix ρ = 1 ∧
      ∀ (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ),
        hsInner (petzAdjoint ρ Y) X = hsInner Y (petzMap ρ X) := by
  have _ := hρ
  have _ := hσ
  have _ := hσ_inv
  have hρA := PositivityProof.partialTraceRight_posDef ρ hρ_inv
  have hAdj := PetzProof.petz_adjoint_identity ρ
    (SpectralProof.sqrtM_conjTranspose ρ)
    (SpectralProof.invSqrtM_conjTranspose (partialTraceRight ρ))
  refine ⟨PetzProof.petz_modular_matrix ρ σ hAdj ?_,
    PetzProof.petz_map_sqrt ρ (SpectralProof.sqrtM_mul_invSqrtM hρA),
    PetzProof.petz_isometry_matrix ρ hAdj ?_, hAdj⟩
  · exact PetzProof.petz_adjoint_modular_petz ρ σ
      (SpectralProof.sqrtM_mul_inv_mul_sqrtM hρ_inv)
      (SpectralProof.invSqrtM_mul_self hρA)
  · exact PetzProof.petz_adjoint_petz ρ
      (SpectralProof.sqrtM_mul_self hρ_inv.posSemidef)
      (SpectralProof.invSqrtM_mul_self_mul_invSqrtM hρA)
