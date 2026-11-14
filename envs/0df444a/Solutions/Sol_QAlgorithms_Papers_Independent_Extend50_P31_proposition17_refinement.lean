-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.proposition17_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:57:27.628222+00:00
-- url     : https://prove2.me/submissions/f2ea5ece-b0a5-4a3c-849c-88c3dbae89b9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.LinearAlgebra.Matrix.Rank
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary19_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint matrixUnitExtension)
private lemma fine_trace_rank (D : Data G A n) (r : Row D) :
    Matrix.trace (fineMatrix D.U D.F r.1.val r.2) = 1 ∧
      Matrix.rank (fineMatrix D.U D.F r.1.val r.2) = 1 := by
  classical
  obtain ⟨C,hC⟩ := fine_projector_coordinate_equiv D
  let Q := fineMatrix D.U D.F r.1.val r.2
  have hc (v : (Fin n × Fin n) → ℂ) : C (Q.mulVec v) = Pi.single r (C v r) := hC r v
  have ht : C.conj Q.mulVecLin = (Matrix.single r r (1 : ℂ)).mulVecLin := by
    apply LinearMap.ext
    intro v
    change C (Q.mulVec (C.symm v)) = _
    rw [hc,C.apply_symm_apply]
    funext s
    simp [Matrix.single_mulVec,Pi.single_apply,Function.update]
  have htrace := LinearMap.trace_conj' Q.mulVecLin C
  have htval := Matrix.trace_toLin'_eq Q
  have htone := Matrix.trace_toLin'_eq (Matrix.single r r (1 : ℂ))
  rw [ht] at htrace
  change LinearMap.trace ℂ _ (Matrix.toLin' (Matrix.single r r (1 : ℂ))) =
    LinearMap.trace ℂ _ (Matrix.toLin' Q) at htrace
  rw [htone,htval,Matrix.trace_single_eq_same] at htrace
  refine ⟨htrace.symm,?_⟩
  have hfixed (x : LinearMap.range Q.mulVecLin) : C x.val = Pi.single r (C x.val r) := by
    obtain ⟨v,hv⟩ := x.property
    rw [← hv]
    change C (Q.mulVec v) = Pi.single r (C (Q.mulVec v) r)
    simp [hc]
  let E : LinearMap.range Q.mulVecLin ≃ₗ[ℂ] ℂ :=
    { toFun := fun x => C x.val r
      invFun := fun z => ⟨C.symm (Pi.single r z),by
        refine ⟨C.symm (Pi.single r z),?_⟩
        apply C.injective
        change C (Q.mulVec (C.symm (Pi.single r z))) = C (C.symm (Pi.single r z))
        simp [hc]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply C.injective
        simpa using (hfixed x).symm
      right_inv := by intro z; simp
      map_add' := by intro x y; simp
      map_smul' := by intro z x; simp }
  change Module.finrank ℂ (LinearMap.range Q.mulVecLin) = 1
  simpa using E.finrank_eq
private lemma central_matrix_eq_fine (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) :
    centralMatrix U F a = ∑ i : Fin (F.dim a), fineMatrix U F a i := by
  ext p q
  simp only [centralMatrix,fineMatrix,character,Matrix.trace,Matrix.diag_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

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

/-- PDF p.12, Proposition 17 Eqs.(56),(57). Trace/rank one are conclusions, not input fields. -/
theorem solution (D : Data G A n) :
    (∀ a : OccurringIrrep D, centralMatrix D.U D.F a.val =
      ∑ i : Fin (D.F.dim a.val), fineMatrix D.U D.F a.val i) ∧
    (∀ r s : Row D, fineMatrix D.U D.F r.1.val r.2 * fineMatrix D.U D.F s.1.val s.2 =
      if r = s then fineMatrix D.U D.F r.1.val r.2 else 0) ∧
    (∀ r : Row D, (fineMatrix D.U D.F r.1.val r.2)ᴴ = fineMatrix D.U D.F r.1.val r.2 ∧
      Matrix.trace (fineMatrix D.U D.F r.1.val r.2) = 1 ∧
      Matrix.rank (fineMatrix D.U D.F r.1.val r.2) = 1) := by
  obtain ⟨hrow,hcentral,hcomp,hadj⟩ := corollary19_refinement D
  obtain ⟨_,hmul,_⟩ := row_representative_calculus n
  refine ⟨fun a => central_matrix_eq_fine _ _ _,?_,?_⟩
  · intro r s
    have h := congrArg rowMatrixRepresentative (hcomp r s)
    rw [hmul,hrow,hrow] at h
    split_ifs with he
    · simpa only [if_pos he,hrow] using h
    · have hz : rowMatrixRepresentative (0 : EndMat n) = 0 := by ext p q; rfl
      simpa only [if_neg he,hz] using h
  · intro r
    refine ⟨?_,fine_trace_rank D r⟩
    have h := congrArg rowMatrixRepresentative (hadj r)
    rw [row_adjoint,hrow] at h
    exact h
