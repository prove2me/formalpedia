-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.proposition13_projectors
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:29:29.761791+00:00
-- url     : https://prove2.me/submissions/65b1478f-ad54-4318-b48f-9700f6868fa6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.LinearAlgebra.Matrix.Rank
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_multiplicity_free_block_scalars
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_central_projector_irrep_action
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition17_refinement
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma central_coordinates (D : Data G A n)
    (T : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ] ((b : OccurringIrrep D) → Fin (D.F.dim b.val) → ℂ))
    (hT : ∀ g v b, T ((tensorConjugate D.U g).mulVec v) b =
      ((D.F.irrep b.val).rho g).mulVec (T v b)) (a : A) (v : (Fin n × Fin n) → ℂ)
    (b : OccurringIrrep D) :
    T ((centralMatrix D.U D.F a).mulVec v) b =
      if a = b.val then T v b else 0 := by
  have h := congrArg (fun M : Mat (D.F.dim b.val) => M.mulVec (T v b))
    (central_projector_irrep_action D.F a b.val)
  simp only [centralMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec,
    map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, hT]
  split_ifs at h ⊢ <;> simpa only [Matrix.smul_mulVec, Matrix.sum_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec] using h

private lemma fine_trace_rank (D : Data G A n) (r : Row D) :
    Matrix.trace (fineMatrix D.U D.F r.1.val r.2) = 1 ∧
      Matrix.rank (fineMatrix D.U D.F r.1.val r.2) = 1 := by
  exact ((proposition17_refinement D).2.2 r).2
private lemma commutant_spectral (D : Data G A n) (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hM : M ∈ representationCommutant (tensorConjugate D.U)) :
    ∃ l : OccurringIrrep D → ℂ, M = ∑ a : OccurringIrrep D, l a • centralMatrix D.U D.F a.val := by
  classical
  obtain ⟨T,hT⟩ := D.decomposition
  let N := T.toLinearMap.comp (M.mulVecLin.comp T.symm.toLinearMap)
  have hTf (g : G) (v : (Fin n × Fin n) → ℂ) :
      T ((tensorConjugate D.U g).mulVec v) =
        fun a => ((D.F.irrep a.val).rho g).mulVec (T v a) := by funext a; exact hT g v a
  have hTi (g : G) (v : (a : OccurringIrrep D) → Fin (D.F.dim a.val) → ℂ) :
      T.symm (fun a => ((D.F.irrep a.val).rho g).mulVec (v a)) =
        (tensorConjugate D.U g).mulVec (T.symm v) := by
    apply T.injective
    rw [T.apply_symm_apply,hTf,T.apply_symm_apply]
  have hN : ∀ g v a, N (fun b => ((D.F.irrep b.val).rho g).mulVec (v b)) a =
      ((D.F.irrep a.val).rho g).mulVec (N v a) := by
    intro g v a
    change T (M.mulVec (T.symm (fun b => ((D.F.irrep b.val).rho g).mulVec (v b)))) a = _
    rw [hTi,Matrix.mulVec_mulVec,hM g,← Matrix.mulVec_mulVec,hT]
    rfl
  obtain ⟨l,hl⟩ := multiplicity_free_block_scalars D.F D.theta N hN
  have hs (v : (Fin n × Fin n) → ℂ) (a : OccurringIrrep D) :
      T (M.mulVec v) a = l a • T v a := by
    simpa [N] using hl (T v) a
  refine ⟨l,?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext a
  change T (M.mulVec v) a = T ((∑ b : OccurringIrrep D, l b • centralMatrix D.U D.F b.val).mulVec v) a
  have hsum : T ((∑ b : OccurringIrrep D, l b • centralMatrix D.U D.F b.val).mulVec v) a =
      ∑ b : OccurringIrrep D, l b • T ((centralMatrix D.U D.F b.val).mulVec v) a := by
    rw [Matrix.sum_mulVec,map_sum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Matrix.smul_mulVec,map_smul]
    rfl
  rw [hs,hsum]
  symm
  calc
    _ = ∑ b : OccurringIrrep D, if b = a then l a • T v a else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [central_coordinates D T hT b.val v a]
      by_cases he : b = a
      · subst b; simp
      · have hn : b.val ≠ a.val := fun h => he (Subtype.ext h)
        simp [hn,he]
    _ = _ := by simp

private lemma central_commutes (D : Data G A n) (a : A) :
    centralMatrix D.U D.F a ∈ representationCommutant (tensorConjugate D.U) := by
  obtain ⟨T,hT⟩ := D.decomposition
  intro g
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext b
  simp only [Matrix.toLin'_apply,← Matrix.mulVec_mulVec,central_coordinates D T hT,hT]
  split_ifs <;> simp

private lemma central_span (D : Data G A n) :
    representationCommutant (tensorConjugate D.U) =
      Submodule.span ℂ (Set.range (fun a : OccurringIrrep D => centralMatrix D.U D.F a.val)) := by
  apply le_antisymm
  · intro M hM
    obtain ⟨l,rfl⟩ := commutant_spectral D M hM
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro M ⟨a,rfl⟩
    exact central_commutes D a.val

private lemma central_orthogonal (D : Data G A n) (a b : OccurringIrrep D) :
    centralMatrix D.U D.F a.val * centralMatrix D.U D.F b.val =
      if a = b then centralMatrix D.U D.F a.val else 0 := by
  obtain ⟨T,hT⟩ := D.decomposition
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext c
  simp only [Matrix.toLin'_apply,← Matrix.mulVec_mulVec,central_coordinates D T hT]
  by_cases hab : a = b
  · subst b
    simp [central_coordinates D T hT]
    all_goals tauto
  · have hc : ¬ (a.val = c.val ∧ b.val = c.val) := by
      rintro ⟨ha,hb⟩
      exact hab (Subtype.ext (ha.trans hb.symm))
    split_ifs <;> simp_all

private lemma central_matrix_eq_fine (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) :
    centralMatrix U F a = ∑ i : Fin (F.dim a), fineMatrix U F a i := by
  ext p q
  simp only [centralMatrix,fineMatrix,character,Matrix.trace,Matrix.diag_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
private lemma central_hermitian (D : Data G A n) (a : OccurringIrrep D) :
    (centralMatrix D.U D.F a.val).IsHermitian := by
  rw [central_matrix_eq_fine]
  change (∑ i : Fin (D.F.dim a.val), fineMatrix D.U D.F a.val i)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ((proposition17_refinement D).2.2 ⟨a,i⟩).1
private lemma central_trace_value (D : Data G A n) (a : OccurringIrrep D) :
    Matrix.trace (centralMatrix D.U D.F a.val) = (D.F.dim a.val : ℂ) := by
  calc
    _ = ∑ i : Fin (D.F.dim a.val), Matrix.trace (fineMatrix D.U D.F a.val i) := by
      rw [central_matrix_eq_fine,Matrix.trace_sum]
    _ = ∑ i : Fin (D.F.dim a.val), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (fine_trace_rank D ⟨a,i⟩).1
    _ = _ := by simp
private lemma central_nonzero (D : Data G A n) (a : OccurringIrrep D) :
    centralMatrix D.U D.F a.val ≠ 0 := by
  intro hz
  have ht := central_trace_value D a
  rw [hz,Matrix.trace_zero] at ht
  have hn : (D.F.dim a.val : ℂ) ≠ 0 := by exact_mod_cast (D.F.irrep a.val).positive.ne'
  exact hn ht.symm
private lemma central_independent (D : Data G A n) :
    LinearIndependent ℂ (fun a : OccurringIrrep D => centralMatrix D.U D.F a.val) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ =>
    M * centralMatrix D.U D.F a.val) hc
  have hh : c a • centralMatrix D.U D.F a.val = 0 := by
    simpa [Matrix.sum_mul,Matrix.smul_mul,central_orthogonal,smul_ite] using h
  exact (smul_eq_zero.mp hh).resolve_right (central_nonzero D a)
private lemma central_sum (D : Data G A n) :
    (∑ a : OccurringIrrep D, centralMatrix D.U D.F a.val) = 1 := by
  classical
  obtain ⟨T,hT⟩ := D.decomposition
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply T.injective
  funext b
  simp only [Matrix.toLin'_apply,Matrix.one_mulVec]
  rw [Matrix.sum_mulVec,map_sum,Finset.sum_apply]
  calc
    _ = ∑ a : OccurringIrrep D, if a = b then T v b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [central_coordinates D T hT a.val v b]
      have he : a.val = b.val ↔ a = b := Subtype.ext_iff.symm
      simp only [he]
    _ = _ := by simp
private lemma central_rank_value (D : Data G A n) (a : OccurringIrrep D) :
    Matrix.rank (centralMatrix D.U D.F a.val) = D.F.dim a.val := by
  let Q := centralMatrix D.U D.F a.val
  have hq : Q * Q = Q := by simpa using central_orthogonal D a a
  have hi : IsIdempotentElem Q.mulVecLin := by
    apply LinearMap.ext
    intro v
    change Q.mulVec (Q.mulVec v) = Q.mulVec v
    rw [Matrix.mulVec_mulVec,hq]
  have ht := ((LinearMap.isProj_range_iff_isIdempotentElem Q.mulVecLin).mpr hi).trace
  have he : LinearMap.trace ℂ _ Q.mulVecLin = Matrix.trace Q := Matrix.trace_toLin'_eq Q
  rw [he] at ht
  have hc := (central_trace_value D a).symm.trans ht
  change (D.F.dim a.val : ℂ) = (Matrix.rank Q : ℂ) at hc
  exact_mod_cast hc.symm


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

/-- PDF p.11, Proposition 13 Eqs.(48)--(50): projectors are the computed Eq.(49) averages. -/
theorem solution (D : Data G A n) :
    representationCommutant (tensorConjugate D.U) =
      Submodule.span ℂ (Set.range (fun a : OccurringIrrep D => centralMatrix D.U D.F a.val)) ∧
    Module.finrank ℂ (representationCommutant (tensorConjugate D.U)) = Fintype.card (OccurringIrrep D) ∧
    (∀ a b : OccurringIrrep D, centralMatrix D.U D.F a.val * centralMatrix D.U D.F b.val =
      if a = b then centralMatrix D.U D.F a.val else 0) ∧
    (∀ a : OccurringIrrep D, (centralMatrix D.U D.F a.val)ᴴ = centralMatrix D.U D.F a.val) ∧
    (∑ a : OccurringIrrep D, centralMatrix D.U D.F a.val) = 1 ∧
    (∀ a : OccurringIrrep D, Matrix.trace (centralMatrix D.U D.F a.val) = (D.F.dim a.val : ℂ) ∧
      Matrix.rank (centralMatrix D.U D.F a.val) = D.F.dim a.val) := by
  refine ⟨central_span D,?_,central_orthogonal D,central_hermitian D,central_sum D,
    fun a => ⟨central_trace_value D a,central_rank_value D a⟩⟩
  rw [central_span D]
  exact finrank_span_eq_card (central_independent D)
