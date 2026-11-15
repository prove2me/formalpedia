-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary15_spectral
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:33:41.707297+00:00
-- url     : https://prove2.me/submissions/88af8f60-9d16-4266-abe4-b2e31fcf4920

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition13_projectors
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma9_covariance
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint matrixUnitExtension)
open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
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

private lemma central_nonzero (D : Data G A n) (a : OccurringIrrep D) :
    centralMatrix D.U D.F a.val ≠ 0 := by
  intro hz
  have ht := ((proposition13_projectors D).2.2.2.2.2 a).1
  rw [hz,Matrix.trace_zero] at ht
  have hn : (D.F.dim a.val : ℂ) ≠ 0 := by exact_mod_cast (D.F.irrep a.val).positive.ne'
  exact hn ht.symm
private lemma central_row (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) :
    rowMatrixRepresentative (centralMap U F a) = centralMatrix U F a := by
  obtain ⟨_,_,hs⟩ := row_representative_calculus n
  have hC (g : G) : rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g := by
    rw [conjugationMap,hs]
    rfl
  ext p q
  simp only [rowMatrixRepresentative,centralMap,centralMatrix,
    LinearMap.smul_apply,LinearMap.sum_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p q) (hC g)
  simpa only [rowMatrixRepresentative] using congrArg (fun z : ℂ => character (F.irrep a) g⁻¹ * z) h
private lemma row_spectral (D : Data G A n) (l : OccurringIrrep D → ℂ) :
    rowMatrixRepresentative (spectralMap D l) = ∑ a, l a • centralMatrix D.U D.F a.val := by
  ext p q
  simp only [rowMatrixRepresentative,spectralMap,LinearMap.sum_apply,LinearMap.smul_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p q) (central_row D.U D.F a.val)
  exact congrArg (fun z : ℂ => l a * z) h
private lemma row_identity : rowMatrixRepresentative (LinearMap.id : EndMat n) = 1 := by
  ext p q
  simp [rowMatrixRepresentative,matrixUnit,Matrix.single_apply,Matrix.one_apply,Prod.ext_iff,ite_and,eq_comm]
private lemma central_map_product (D : Data G A n) (a b : OccurringIrrep D) :
    (centralMap D.U D.F a.val).comp (centralMap D.U D.F b.val) =
      if a = b then centralMap D.U D.F a.val else 0 := by
  apply row_injective
  obtain ⟨_,hc,_⟩ := row_representative_calculus n
  rw [hc,central_row,central_row,(proposition13_projectors D).2.2.1]
  split_ifs
  · exact (central_row _ _ _).symm
  · ext p q; rfl


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

/-- PDF pp.11--12, Corollary 15 and Remark 16. Equal eigenvalues across sectors are allowed. -/
theorem solution (D : Data G A n) (Phi : EndMat n) (hPhi : IsIrrepCovariant D.U Phi) :
    (∃ l : OccurringIrrep D → ℂ, Phi = spectralMap D l ∧
      ∀ a : OccurringIrrep D,
        (∃ X : Mat n, X ≠ 0 ∧ centralMap D.U D.F a.val X = X) ∧
        ∀ X : Mat n, Phi (centralMap D.U D.F a.val X) = l a • centralMap D.U D.F a.val X) ∧
    (∀ a : OccurringIrrep D, rowMatrixRepresentative (centralMap D.U D.F a.val) = centralMatrix D.U D.F a.val) ∧
    (∀ a b : OccurringIrrep D, (centralMap D.U D.F a.val).comp (centralMap D.U D.F b.val) =
      if a = b then centralMap D.U D.F a.val else 0) ∧
    (∀ a : OccurringIrrep D, hsAdjoint (centralMap D.U D.F a.val) = centralMap D.U D.F a.val) ∧
    (∑ a : OccurringIrrep D, centralMap D.U D.F a.val) = LinearMap.id := by
  classical
  have hm := (lemma9_covariance (by infer_instance) D.U Phi).mp hPhi
  rw [(proposition13_projectors D).1] at hm
  obtain ⟨l,hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
  have he : Phi = spectralMap D l := by
    apply row_injective
    rw [row_spectral]
    exact hl.symm
  refine ⟨⟨l,he,?_⟩,fun a => central_row _ _ _,central_map_product D,?_,?_⟩
  · intro a
    refine ⟨?_,?_⟩
    · have hn : centralMap D.U D.F a.val ≠ 0 := by
        intro hz
        apply central_nonzero D a
        rw [← central_row,hz]
        ext p q; rfl
      have hne : ¬ ∀ X, centralMap D.U D.F a.val X = 0 := by
        intro h
        exact hn (LinearMap.ext h)
      obtain ⟨X,hX⟩ := not_forall.mp hne
      refine ⟨centralMap D.U D.F a.val X,hX,?_⟩
      have h := congrArg (fun f : EndMat n => f X) (central_map_product D a a)
      simpa using h
    · intro X
      have hh : (spectralMap D l).comp (centralMap D.U D.F a.val) = l a • centralMap D.U D.F a.val := by
        apply LinearMap.ext
        intro Y
        change (spectralMap D l) (centralMap D.U D.F a.val Y) = _
        simp only [spectralMap,LinearMap.sum_apply,LinearMap.smul_apply]
        calc
          _ = ∑ b : OccurringIrrep D, if b = a then l a • centralMap D.U D.F a.val Y else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            have h := congrArg (fun f : EndMat n => f Y) (central_map_product D b a)
            by_cases hb : b = a
            · subst b
              simpa using congrArg (fun Z : Mat n => l a • Z) h
            · have hz : centralMap D.U D.F b.val (centralMap D.U D.F a.val Y) = 0 := by
                simpa [hb] using h
              simp [hb,hz]
          _ = _ := by simp
      rw [he]
      exact congrArg (fun f : EndMat n => f X) hh
  · intro a
    apply row_injective
    rw [row_adjoint,central_row]
    exact (proposition13_projectors D).2.2.2.1 a
  · apply row_injective
    have h := row_spectral D (fun _ => 1)
    simpa only [spectralMap,one_smul,(proposition13_projectors D).2.2.2.2.1,row_identity] using h
