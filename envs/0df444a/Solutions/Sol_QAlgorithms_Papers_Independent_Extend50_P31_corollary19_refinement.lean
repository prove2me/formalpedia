-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary19_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:55:04.286195+00:00
-- url     : https://prove2.me/submissions/c0c0cdd1-3e3f-4aa1-9613-84a8b7b075bd

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint matrixUnitExtension)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
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

private lemma rho_inverse {n : ℕ} (U : UnitaryIrrep G n) (g : G) : U.rho g⁻¹ = (U.rho g)ᴴ := by
  calc
    U.rho g⁻¹ = U.rho g⁻¹ * (U.rho g * (U.rho g)ᴴ) := by rw [(U.unitary g).2,Matrix.mul_one]
    _ = (U.rho g⁻¹ * U.rho g) * (U.rho g)ᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = (U.rho g)ᴴ := by rw [← U.mul,inv_mul_cancel,U.one,Matrix.one_mul]

private lemma fine_hermitian (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (i : Fin (F.dim a)) :
    (fineMatrix U F a i).IsHermitian := by
  have hterm (g : G) (p q : Fin n × Fin n) :
      conj ((F.irrep a).rho g⁻¹ i i * tensorConjugate U g q p) =
        (F.irrep a).rho g i i * tensorConjugate U g⁻¹ p q := by
    simp [tensorConjugate,Matrix.kronecker_apply,rho_inverse,Matrix.conjTranspose_apply,
      map_mul,mul_comm,mul_left_comm,mul_assoc]
  apply Matrix.ext
  intro p q
  have h := Equiv.sum_comp (Equiv.inv G)
    (fun g : G => (F.irrep a).rho g⁻¹ i i * tensorConjugate U g p q)
  simp only [Equiv.inv_apply,inv_inv] at h
  change conj (fineMatrix U F a i q p) = fineMatrix U F a i p q
  simp only [fineMatrix,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  have hc : conj ((F.dim a : ℂ) / Fintype.card G) = ((F.dim a : ℂ) / Fintype.card G) := by simp
  rw [map_mul,hc,map_sum]
  congr 1
  calc
    _ = ∑ g : G, (F.irrep a).rho g i i * tensorConjugate U g⁻¹ p q := by
      apply Finset.sum_congr rfl
      intro g hg
      exact hterm g p q
    _ = _ := h
private lemma fine_orthogonal (D : Data G A n) (r s : Row D) :
    fineMatrix D.U D.F r.1.val r.2 * fineMatrix D.U D.F s.1.val s.2 =
      if r = s then fineMatrix D.U D.F r.1.val r.2 else 0 := by
  classical
  obtain ⟨C,hC⟩ := fine_projector_coordinate_equiv D
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply C.injective
  simp only [Matrix.toLin'_apply,← Matrix.mulVec_mulVec,hC]
  split_ifs with hrs
  · subst s
    simp [hC]
  · simp [hrs,Pi.single_apply,Ne.symm hrs]

private lemma central_eq_fine (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) :
    centralMap U F a = ∑ i : Fin (F.dim a), fineMap U F a i := by
  apply LinearMap.ext
  intro X
  ext p q
  simp only [centralMap,fineMap,character,Matrix.trace,Matrix.diag_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma row_injective : Function.Injective (rowMatrixRepresentative : EndMat n → _) := by
  intro Phi Psi he
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  apply LinearMap.ext
  intro X
  apply rowVec.injective
  rw [ha,he,← ha]

private lemma row_adjoint (Phi : EndMat n) : rowMatrixRepresentative (hsAdjoint Phi) =
    (rowMatrixRepresentative Phi)ᴴ := by
  ext p q
  simp [rowMatrixRepresentative,hsAdjoint,matrixUnitExtension,matrixUnit,
    Matrix.single_apply,ite_and,Matrix.conjTranspose_apply]


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

/-- PDF p.12, Corollary 19 Eqs.(59),(60). -/
theorem solution (D : Data G A n) :
    (∀ r : Row D, rowMatrixRepresentative (fineMap D.U D.F r.1.val r.2) = fineMatrix D.U D.F r.1.val r.2) ∧
    (∀ a : OccurringIrrep D, centralMap D.U D.F a.val =
      ∑ i : Fin (D.F.dim a.val), fineMap D.U D.F a.val i) ∧
    (∀ r s : Row D, (fineMap D.U D.F r.1.val r.2).comp (fineMap D.U D.F s.1.val s.2) =
      if r = s then fineMap D.U D.F r.1.val r.2 else 0) ∧
    (∀ r : Row D, hsAdjoint (fineMap D.U D.F r.1.val r.2) = fineMap D.U D.F r.1.val r.2) := by
  refine ⟨fun r => fine_row _ _ _ _,fun a => central_eq_fine _ _ _,?_,?_⟩
  · intro r s
    apply row_injective
    obtain ⟨_,hcomp,_⟩ := row_representative_calculus n
    rw [hcomp,fine_row,fine_row,fine_orthogonal]
    split_ifs with h
    · exact (fine_row _ _ _ _).symm
    · ext p q; rfl
  · intro r
    apply row_injective
    rw [row_adjoint,fine_row]
    exact fine_hermitian D.U D.F r.1.val r.2
