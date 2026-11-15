-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary22_basis
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:12:59.396762+00:00
-- url     : https://prove2.me/submissions/5bacc6dd-9bf1-4a7e-a645-416c061304e9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition20_eigenmatrices
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open QAlgorithms.Papers.Independent.Information100.P75 (phase)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma hs_coordinates (X Y : Mat n) : hs X Y = ∑ p : Fin n × Fin n, conj (rowVec X p) * rowVec Y p := by
  simp [hs,res,PiLp.inner_apply,RCLike.inner_apply,rowVec,mul_comm]
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

/-- PDF pp.13--14, Corollary 22 and Remark 23: exactly ONE pivot per fine sector. -/
theorem solution (D : Data G A n) (P : Pivots D) :
    Fintype.card (Row D) = n^2 ∧
    (∀ r s, hs (eigenmatrix D P r) (eigenmatrix D P s) = if r = s then 1 else 0) ∧
    Submodule.span ℂ (Set.range (eigenmatrix D P)) = ⊤ := by
  classical
  obtain ⟨C,hC⟩ := fine_projector_coordinate_equiv D
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  have hnorm (r : Row D) : hs (eigenmatrix D P r) (eigenmatrix D P r) = 1 :=
    ((proposition20_eigenmatrices D).2.1 r (P.pivot r) (P.positive r)).1
  have hcoords (r : Row D) : C (rowVec (eigenmatrix D P r)) =
      Pi.single r (C (rowVec (eigenmatrix D P r)) r) := by
    have h := hC r (rowVec (eigenmatrix D P r))
    have hf : fineMap D.U D.F r.1.val r.2 (eigenmatrix D P r) = eigenmatrix D P r := by
      simpa [eigenmatrix] using ((proposition20_eigenmatrices D).2.1 r (P.pivot r) (P.positive r)).2 r
    have hh := congrArg (fun Z : Mat n => C (rowVec Z)) hf
    rw [ha,fine_row] at hh
    rw [hh] at h
    exact h
  have hn (r : Row D) : C (rowVec (eigenmatrix D P r)) r ≠ 0 := by
    intro hz
    have he : C (rowVec (eigenmatrix D P r)) = 0 := by rw [hcoords,hz]; simp
    have hr : rowVec (eigenmatrix D P r) = 0 := C.injective (by simpa using he)
    have hx : eigenmatrix D P r = 0 := rowVec.injective (by simpa using hr)
    have h := hnorm r
    simp [hx,hs_coordinates] at h
  refine ⟨?_,?_,?_⟩
  · have h := C.finrank_eq
    simpa [Module.finrank_fintype_fun_eq_card,Nat.pow_two] using h.symm
  · intro r s
    by_cases hrs : r = s
    · subst s; simpa using hnorm r
    · obtain ⟨t,ht⟩ := (proposition20_eigenmatrices D).2.2.1 r s (P.pivot r) (P.pivot s)
        (P.positive r) (P.positive s)
      simpa [eigenmatrix,hrs] using ht
  · apply top_unique
    intro X hX
    let c : Row D → ℂ := fun r => C (rowVec X) r / C (rowVec (eigenmatrix D P r)) r
    have he : X = ∑ r : Row D, c r • eigenmatrix D P r := by
      apply rowVec.injective
      apply C.injective
      calc
        _ = ∑ r : Row D, c r • Pi.single r (C (rowVec (eigenmatrix D P r)) r) := by
          funext s
          simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,c,hn]
        _ = _ := by
          simp only [map_sum,map_smul]
          apply Finset.sum_congr rfl
          intro r hr
          exact congrArg (fun w : Row D → ℂ => c r • w) (hcoords r).symm
    rw [he]
    apply Submodule.sum_mem
    intro r hr
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r,rfl⟩)
