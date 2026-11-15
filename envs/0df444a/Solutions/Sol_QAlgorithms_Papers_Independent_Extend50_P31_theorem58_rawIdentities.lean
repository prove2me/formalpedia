-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.theorem58_rawIdentities
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:20:39.306417+00:00
-- url     : https://prove2.me/submissions/567f2fdb-d216-4372-851b-c6c294976864

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_raw_eigenmatrix_gram
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition17_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_central_projector_irrep_action
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)
open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma raw_inner (D : Data G A n) (r s : Row D) (p q : Fin n × Fin n) :
    hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F s.1.val s.2 q) =
      if r = s then fineMatrix D.U D.F r.1.val r.2 p q else 0 := by
  exact raw_eigenmatrix_gram D r s p q
private lemma fine_trace_rank (D : Data G A n) (r : Row D) :
    Matrix.trace (fineMatrix D.U D.F r.1.val r.2) = 1 ∧
      Matrix.rank (fineMatrix D.U D.F r.1.val r.2) = 1 := by
  exact ((proposition17_refinement D).2.2 r).2
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

private lemma fine_coefficient (F : IrrepFamily G A) (a : A) (i : Fin (F.dim a)) :
    ((F.dim a : ℂ) / Fintype.card G) * (∑ g : G, (F.irrep a).rho g⁻¹ i i) =
      if a = F.trivial then 1 else 0 := by
  classical
  have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases ha : a = F.trivial
  · subst a
    simp [F.trivial_action,F.trivial_dim,hg]
  · have h := central_projector_irrep_action F F.trivial a
    have he := congrArg (fun M : Mat (F.dim a) => M i i) h
    have hdiag : (Fintype.card G : ℂ)⁻¹ * (∑ g : G, (F.irrep a).rho g i i) = 0 := by
      simpa [character,F.trivial_action,Matrix.trace_one,F.trivial_dim,Matrix.sum_apply,Matrix.smul_apply,eq_comm,ha] using he
    have hs : (∑ g : G, (F.irrep a).rho g i i) = 0 :=
      (mul_eq_zero.mp hdiag).resolve_left (inv_ne_zero hg)
    have hi := Equiv.sum_comp (Equiv.inv G) (fun g : G => (F.irrep a).rho g i i)
    change (∑ g : G, (F.irrep a).rho g⁻¹ i i) = _ at hi
    rw [hi,hs]
    simp [ha]
private lemma fine_trace_value (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (i : Fin (F.dim a)) (X : Mat n) :
    Matrix.trace (fineMap U F a i X) = (if a = F.trivial then 1 else 0) * Matrix.trace X := by
  have ht (g : G) : Matrix.trace (conjugationMap U g X) = Matrix.trace X := by
    change Matrix.trace (U.rho g * (X * (U.rho g)ᴴ)) = _
    rw [Matrix.trace_mul_comm,Matrix.mul_assoc,(U.unitary g).1,Matrix.mul_one]
  simp only [fineMap,LinearMap.smul_apply,LinearMap.sum_apply,Matrix.trace_smul,
    Matrix.trace_sum,smul_eq_mul,ht,← Finset.sum_mul,← mul_assoc,fine_coefficient]
private lemma fine_one (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (i : Fin (F.dim a)) :
    fineMap U F a i 1 = if a = F.trivial then (1 : Mat n) else 0 := by
  have ht (g : G) : conjugationMap U g (1 : Mat n) = 1 := by
    change U.rho g * (1 * (U.rho g)ᴴ) = 1
    simpa using (U.unitary g).2
  simp only [fineMap,LinearMap.smul_apply,LinearMap.sum_apply,ht,← Finset.sum_smul,
    smul_smul,fine_coefficient]
  split_ifs <;> simp


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

/-- PDF pp.31--32, Theorem 58 Eqs.(157)--(160), proof p.40 Eq.(192).
SOURCE CORRECTION: these are raw W, not normalized Eq.(62) V. At id and a diagonal
pivot, W=I/n has squared HS norm 1/n. Proof Eq.(194) also needs the omitted sum over s. -/
theorem solution (D : Data G A n) :
    (∀ r : Row D, ∀ p : Fin n × Fin n,
      hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F r.1.val r.2 p) =
        fineMatrix D.U D.F r.1.val r.2 p p) ∧
    (∀ r : Row D, (∑ p : Fin n × Fin n,
      hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F r.1.val r.2 p)) = 1) ∧
    (∀ p : Fin n × Fin n, (∑ r : Row D, rawMatrix D.U D.F r.1.val r.2 p) = matrixUnit p.1 p.2) ∧
    (∀ r : Row D, (∑ s : Fin n, rawMatrix D.U D.F r.1.val r.2 (s,s)) =
      if r.1.val = D.F.trivial then 1 else 0) ∧
    (∀ r : Row D, ∀ p : Fin n × Fin n, Matrix.trace (rawMatrix D.U D.F r.1.val r.2 p) =
      if r.1.val = D.F.trivial ∧ p.1 = p.2 then 1 else 0) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r p; simpa using raw_inner D r r p p
  · intro r
    simpa [raw_inner,Matrix.trace,Matrix.diag_apply] using (fine_trace_rank D r).1
  · intro p
    obtain ⟨C,hC⟩ := fine_projector_coordinate_equiv D
    obtain ⟨ha,_,_⟩ := row_representative_calculus n
    apply rowVec.injective
    apply C.injective
    simp only [map_sum,rawMatrix,ha,fine_row,hC]
    funext s
    simp [Finset.sum_apply,Pi.single_apply]
  · intro r
    have hb : (∑ s : Fin n, matrixUnit s s) = (1 : Mat n) := by
      ext i j
      simp [matrixUnit,Matrix.single_apply,ite_and,Matrix.sum_apply,Matrix.one_apply]
    change (∑ s : Fin n, fineMap D.U D.F r.1.val r.2 (matrixUnit s s)) = _
    rw [← map_sum,hb,fine_one]
  · intro r p
    rw [rawMatrix,fine_trace_value]
    by_cases hd : p.1 = p.2
    · simp [hd,matrixUnit]
    · simp [matrixUnit,Matrix.trace_single_eq_of_ne,hd]
