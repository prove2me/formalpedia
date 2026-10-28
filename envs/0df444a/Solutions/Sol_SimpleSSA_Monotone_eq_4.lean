-- Prove2me | solution 1 for SimpleSSA.Monotone.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:23:05.739985+00:00
-- url     : https://prove2.me/submissions/e889871a-cbd1-49c3-9121-d71054f9ae8a

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic
import Theorems.Thm_TroppMatrixConcentration_ch8_log_operator_concave
import Theorems.Thm_TroppMatrixConcentration_ch8_jensen_isometric_compression
import Theorems.Thm_SimpleSSA_Monotone_eq_7
import Theorems.Thm_SimpleSSA_Monotone_petz_map_properties


open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone.MainPositivityProof

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

omit [DecidableEq A] [DecidableEq B] in
lemma trace_partialTraceRight (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceRight ρ) = Matrix.trace ρ := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq B] in
lemma partialTraceRight_density (ρ : Matrix (A × B) (A × B) ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (partialTraceRight ρ) := by
  exact ⟨partialTraceRight_posSemidef ρ hρ.1, (trace_partialTraceRight ρ).trans hρ.2⟩

lemma modularOp_posDef (ρ σ : Matrix A A ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    (modularOp ρ σ).PosDef :=
  hσ.kronecker hρ.inv.transpose

lemma spectrum_pos_of_posDef (ρ : Matrix A A ℂ) (hρ : ρ.PosDef) :
    spectrum ℝ ρ ⊆ Set.Ioi 0 := by
  intro x hx
  exact hρ.isStrictlyPositive.spectrum_pos hx

lemma neglog_matrixFunction (ρ : Matrix A A ℂ) :
    ch8_matrixFunction (fun x => -Real.log x) ρ = -matrixLog ρ := by
  simp [ch8_matrixFunction, matrixLog, cfc_neg]

end SimpleSSA.Monotone.MainPositivityProof


open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone.JensenProof

open TroppMatrixConcentration

/-- Jensen's inequality for negative logarithm, evaluated on an arbitrary vector. -/
lemma neglog_compression_quadratic {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (D : Matrix ι ι ℂ) (hD : D.PosDef)
    (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) (v : κ → ℂ) :
    (star v ⬝ᵥ (-(matrixLog (Uᴴ * D * U)) *ᵥ v)).re ≤
      (star (U *ᵥ v) ⬝ᵥ (-(matrixLog D) *ᵥ (U *ᵥ v))).re := by
  have hj := ch8_jensen_isometric_compression (Set.Ioi 0) (fun x => -Real.log x)
    ch8_log_operator_concave D hD.isHermitian
    (fun _ hx => hD.isStrictlyPositive.spectrum_pos hx) U hU
  change (Uᴴ * ch8_matrixFunction (fun x => -Real.log x) D * U -
    ch8_matrixFunction (fun x => -Real.log x) (Uᴴ * D * U)).PosSemidef at hj
  simp only [ch8_matrixFunction, cfc_neg] at hj
  change (Uᴴ * -(matrixLog D) * U - -(matrixLog (Uᴴ * D * U))).PosSemidef at hj
  have hq := (Complex.nonneg_iff.mp (hj.dotProduct_mulVec_nonneg v)).1
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hq
  have heq : star v ⬝ᵥ ((Uᴴ * -(matrixLog D) * U) *ᵥ v) =
      star (U *ᵥ v) ⬝ᵥ (-(matrixLog D) *ᵥ (U *ᵥ v)) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [heq] at hq
  exact sub_nonneg.mp hq

end SimpleSSA.Monotone.JensenProof


open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

noncomputable section

namespace SimpleSSA.Monotone.MainVectorizationProof

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

def petzLinear (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun := petzMap ρ
  map_add' X Y := by simp [petzMap, Matrix.add_mul, Matrix.add_kronecker]
  map_smul' c X := by simp [petzMap, Matrix.smul_kronecker]

lemma petzMatrix_mulVec (ρ : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    petzMatrix ρ *ᵥ vecHS X = vecHS (petzMap ρ X) :=
  linear_matrix_mulVec (petzLinear ρ) X

end SimpleSSA.Monotone.MainVectorizationProof

open SimpleSSA.Monotone


open TroppMatrixConcentration QAlgorithms WildeQIT

/-- (4), p. 2, proved in §3 for invertible states (p. 3): monotonicity of the relative entropy
under discarding `B`, `S(ρ_A‖σ_A) ≤ S(ρ_AB‖σ_AB)`. -/
theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ σ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef)
    (hσ : IsDensityMatrix σ) (hσ_inv : σ.PosDef) :
    relEntropy (partialTraceRight ρ) (partialTraceRight σ) ≤ relEntropy ρ σ := by
  have hρA := MainPositivityProof.partialTraceRight_posDef ρ hρ_inv
  have hσA := MainPositivityProof.partialTraceRight_posDef σ hσ_inv
  have hρAd := MainPositivityProof.partialTraceRight_density ρ hρ
  have hσAd := MainPositivityProof.partialTraceRight_density σ hσ
  obtain ⟨hcompression, hsqrt, hisometry, _⟩ :=
    petz_map_properties ρ σ hρ hρ_inv hσ hσ_inv
  have hquadratic := JensenProof.neglog_compression_quadratic
    (modularOp ρ σ) (MainPositivityProof.modularOp_posDef ρ σ hρ_inv hσ_inv)
    (petzMatrix ρ) hisometry (vecHS (sqrtM (partialTraceRight ρ)))
  have hvec : petzMatrix ρ *ᵥ vecHS (sqrtM (partialTraceRight ρ)) = vecHS (sqrtM ρ) := by
    rw [MainVectorizationProof.petzMatrix_mulVec, hsqrt]
  have hleft : relEntropy (partialTraceRight ρ) (partialTraceRight σ) =
      (star (vecHS (sqrtM (partialTraceRight ρ))) ⬝ᵥ
        (-(matrixLog (modularOp (partialTraceRight ρ) (partialTraceRight σ))) *ᵥ
          vecHS (sqrtM (partialTraceRight ρ)))).re := by
    simpa only [Complex.ofReal_re, MainVectorizationProof.hsInner_applyHS] using
      congrArg Complex.re (eq_7 (partialTraceRight ρ) (partialTraceRight σ) hρAd hρA hσAd hσA)
  have hright : relEntropy ρ σ =
      (star (vecHS (sqrtM ρ)) ⬝ᵥ (-(matrixLog (modularOp ρ σ)) *ᵥ vecHS (sqrtM ρ))).re := by
    simpa only [Complex.ofReal_re, MainVectorizationProof.hsInner_applyHS] using
      congrArg Complex.re (eq_7 ρ σ hρ hρ_inv hσ hσ_inv)
  rw [hleft, hright]
  simpa only [hcompression, hvec] using hquadratic

