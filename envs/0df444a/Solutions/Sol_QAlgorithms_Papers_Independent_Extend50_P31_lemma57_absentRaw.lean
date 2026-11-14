-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma57_absentRaw
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:46:00.172043+00:00
-- url     : https://prove2.me/submissions/dfa63d06-9e14-4a50-99b3-bc2ac01d0404

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

private lemma fine_absent (D : Data G A n) (a : A) (ha : a ∉ D.theta) (i : Fin (D.F.dim a)) :
    fineMatrix D.U D.F a i = 0 := by
  obtain ⟨T,hT⟩ := D.decomposition
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext b
  rw [Matrix.toLin'_apply,fine_coordinates D T hT]
  have hn : a ≠ b.val := fun he => ha (he ▸ b.property)
  simp [hn,Matrix.toLin'_apply]


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

/-- PDF p.31, Lemma 57 Eq.(156): raw W, so absent labels and zero pivots are meaningful. -/
theorem solution (D : Data G A n) (a : A) (ha : a ∉ D.theta)
    (i : Fin (D.F.dim a)) (p : Fin n × Fin n) :
    rawMatrix D.U D.F a i p = 0 := by
  obtain ⟨hact,_,_⟩ := row_representative_calculus n
  apply rowVec.injective
  change rowVec (fineMap D.U D.F a i (matrixUnit p.1 p.2)) = rowVec 0
  rw [hact,fine_row,fine_absent D a ha,Matrix.zero_mulVec,map_zero]

