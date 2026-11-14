-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary24_vectorization
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:48:23.861382+00:00
-- url     : https://prove2.me/submissions/a0e11b5d-f503-4323-93ab-6fa7292791c0

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_irrep_action
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44
open QAlgorithms.Papers.Independent.Dependency50.P16
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma fine_coordinates (D : Data G A n)
    (T : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ] ((b : OccurringIrrep D) → Fin (D.F.dim b.val) → ℂ))
    (hT : ∀ g v b, T ((tensorConjugate D.U g).mulVec v) b =
      ((D.F.irrep b.val).rho g).mulVec (T v b))
    (a : A) (i : Fin (D.F.dim a)) (v : (Fin n × Fin n) → ℂ) (b : OccurringIrrep D) :
    T ((fineMatrix D.U D.F a i).mulVec v) b =
      (if h : a = b.val then Matrix.single (Fin.cast (congrArg D.F.dim h) i)
        (Fin.cast (congrArg D.F.dim h) i) 1 else 0).mulVec (T v b) := by
  have h := congrArg (fun M : Mat (D.F.dim b.val) => M.mulVec (T v b))
    (fine_projector_irrep_action D.F a b.val i)
  simp only [fineMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec,
    map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, hT]
  simpa only [Matrix.smul_mulVec, Matrix.sum_mulVec] using h

private lemma fine_row (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (i : Fin (F.dim a)) :
    rowMatrixRepresentative (fineMap U F a i) = fineMatrix U F a i := by
  obtain ⟨_,_,hs⟩ := row_representative_calculus n
  have hC (g : G) : rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g := by
    rw [conjugationMap,hs]
    rfl
  ext p q
  simp only [rowMatrixRepresentative,fineMap,fineMatrix,
    LinearMap.smul_apply,LinearMap.sum_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p q) (hC g)
  simpa only [rowMatrixRepresentative] using congrArg (fun z : ℂ => (F.irrep a).rho g⁻¹ i i * z) h

private lemma fine_idempotent (D : Data G A n) (a : A) (i : Fin (D.F.dim a)) :
    fineMatrix D.U D.F a i * fineMatrix D.U D.F a i = fineMatrix D.U D.F a i := by
  obtain ⟨T,hT⟩ := D.decomposition
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext b
  simp only [Matrix.toLin'_apply,← Matrix.mulVec_mulVec,fine_coordinates D T hT]
  split_ifs with hab
  · simp [Matrix.mulVec_single_one,Matrix.single_apply,ite_and]
  · simp


set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.14, Corollary 24 Eq.(69); the ambient dimension is n squared. -/
theorem solution (D : Data G A n) (P : Pivots D) (r : Row D) :
    (fineMatrix D.U D.F r.1.val r.2).mulVec (rowVec (eigenmatrix D P r)) =
      rowVec (eigenmatrix D P r) := by
  obtain ⟨hact,_,_⟩ := row_representative_calculus n
  have hrow : rowVec (eigenmatrix D P r) =
      ((Real.sqrt (pivotWeight D.U D.F r.1.val r.2 (P.pivot r)) : ℂ)⁻¹) •
        (fineMatrix D.U D.F r.1.val r.2).mulVec (rowVec (matrixUnit (P.pivot r).1 (P.pivot r).2)) := by
    simp only [eigenmatrix,normalizedMatrix,rawMatrix,map_smul,hact,fine_row]
  rw [hrow,Matrix.mulVec_smul,Matrix.mulVec_mulVec,fine_idempotent]
