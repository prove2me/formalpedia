-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.proposition20_eigenmatrices
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:03:26.959862+00:00
-- url     : https://prove2.me/submissions/76d5b857-b07b-4838-a070-3024c667c546

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition17_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary19_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_raw_eigenmatrix_gram
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open QAlgorithms.Papers.Independent.Information100.P75 (phase)
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

private lemma fine_trace_rank (D : Data G A n) (r : Row D) :
    Matrix.trace (fineMatrix D.U D.F r.1.val r.2) = 1 ∧
      Matrix.rank (fineMatrix D.U D.F r.1.val r.2) = 1 := by
  exact ((proposition17_refinement D).2.2 r).2
private lemma fine_orthogonal (D : Data G A n) (r s : Row D) :
    fineMatrix D.U D.F r.1.val r.2 * fineMatrix D.U D.F s.1.val s.2 =
      if r = s then fineMatrix D.U D.F r.1.val r.2 else 0 := by
  exact (proposition17_refinement D).2.1 r s
private lemma hs_coordinates (X Y : Mat n) : hs X Y = ∑ p : Fin n × Fin n, conj (rowVec X p) * rowVec Y p := by
  simp [hs,res,PiLp.inner_apply,RCLike.inner_apply,rowVec,mul_comm]
private lemma hs_smul_both (X Y : Mat n) (c d : ℂ) : hs (c • X) (d • Y) = conj c * d * hs X Y := by
  simp [hs_coordinates,map_smul,map_mul,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]
private lemma raw_inner (D : Data G A n) (r s : Row D) (p q : Fin n × Fin n) :
    hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F s.1.val s.2 q) =
      if r = s then fineMatrix D.U D.F r.1.val r.2 p q else 0 := by
  exact raw_eigenmatrix_gram D r s p q
private lemma positive_pivot (D : Data G A n) (r : Row D) :
    ∃ p : Fin n × Fin n, 0 < pivotWeight D.U D.F r.1.val r.2 p := by
  by_contra h
  push_neg at h
  have ht := congrArg Complex.re (fine_trace_rank D r).1
  have hh : (∑ p : Fin n × Fin n, pivotWeight D.U D.F r.1.val r.2 p) = 1 := by
    simpa [Matrix.trace,pivotWeight] using ht
  have hle : (∑ p : Fin n × Fin n, pivotWeight D.U D.F r.1.val r.2 p) ≤ 0 :=
    Finset.sum_nonpos fun p hp => h p
  linarith
private lemma normalized_inner_self (D : Data G A n) (r : Row D) (p : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p) :
    hs (normalizedMatrix D.U D.F r.1.val r.2 p) (normalizedMatrix D.U D.F r.1.val r.2 p) = 1 := by
  let w := pivotWeight D.U D.F r.1.val r.2 p
  have hw : 0 < w := hp
  have hd : fineMatrix D.U D.F r.1.val r.2 p p = (w : ℂ) := by
    have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p p)
      (((proposition17_refinement D).2.2 r).1)
    have hi : (fineMatrix D.U D.F r.1.val r.2 p p).im = 0 :=
      Complex.conj_eq_iff_im.mp h
    apply Complex.ext
    · rfl
    · simpa using hi
  have hs : (Real.sqrt w : ℂ)^2 = (w : ℂ) := by exact_mod_cast Real.sq_sqrt hw.le
  have hn : (Real.sqrt w : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hw).ne'
  simp only [normalizedMatrix,hs_smul_both,raw_inner,if_pos rfl,hd]
  change conj ((Real.sqrt w : ℂ)⁻¹) * (Real.sqrt w : ℂ)⁻¹ * (w : ℂ) = 1
  rw [map_inv₀,Complex.conj_ofReal]
  field_simp
  exact hs.symm
private lemma normalized_fixed (D : Data G A n) (r s : Row D) (p : Fin n × Fin n) :
    fineMap D.U D.F s.1.val s.2 (normalizedMatrix D.U D.F r.1.val r.2 p) =
      if s = r then normalizedMatrix D.U D.F r.1.val r.2 p else 0 := by
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  apply rowVec.injective
  simp only [normalizedMatrix,rawMatrix,map_smul,ha,fine_row,Matrix.mulVec_smul,
    Matrix.mulVec_mulVec,fine_orthogonal]
  split_ifs with h
  · subst s
    simp only [map_smul,ha,fine_row]
  · simp

private lemma unit_fixed_phase (D : Data G A n) (r : Row D) (X Y : Mat n)
    (hx : hs X X = 1) (hy : hs Y Y = 1)
    (hfx : fineMap D.U D.F r.1.val r.2 X = X)
    (hfy : fineMap D.U D.F r.1.val r.2 Y = Y) : ∃ t : ℝ, Y = phase t • X := by
  classical
  obtain ⟨C,hC⟩ := fine_projector_coordinate_equiv D
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  have hcX : C (rowVec X) = Pi.single r (C (rowVec X) r) := by
    have h := hC r (rowVec X)
    have hh := congrArg (fun Z : Mat n => C (rowVec Z)) hfx
    rw [ha,fine_row] at hh
    rw [hh] at h
    exact h
  have hcY : C (rowVec Y) = Pi.single r (C (rowVec Y) r) := by
    have h := hC r (rowVec Y)
    have hh := congrArg (fun Z : Mat n => C (rowVec Z)) hfy
    rw [ha,fine_row] at hh
    rw [hh] at h
    exact h
  have hn : C (rowVec X) r ≠ 0 := by
    intro hz
    have hcz : C (rowVec X) = 0 := by rw [hcX,hz]; simp
    have hrz : rowVec X = 0 := C.injective (by simpa using hcz)
    have hX : X = 0 := rowVec.injective (by simpa using hrz)
    simp [hX,hs_coordinates] at hx
  let c : ℂ := C (rowVec Y) r / C (rowVec X) r
  have he : Y = c • X := by
    apply rowVec.injective
    apply C.injective
    rw [map_smul,map_smul,hcX,hcY]
    funext s
    by_cases hs : s = r
    · subst s
      simp [Pi.single_apply,c,hn]
    · simp [Pi.single_apply,hs]
  have hu : conj c * c = 1 := by
    rw [he,hs_smul_both,hx,mul_one] at hy
    exact hy
  have hnorm : ‖c‖ = 1 := by
    have h := congrArg norm hu
    simp only [norm_mul,Complex.norm_conj,norm_one] at h
    nlinarith [norm_nonneg c]
  obtain ⟨t,ht⟩ := (Complex.norm_eq_one_iff c).mp hnorm
  exact ⟨t,by simpa only [phase,ht] using he⟩

private lemma hs_smul_right (X Y : Mat n) (c : ℂ) : hs X (c • Y) = c * hs X Y := by
  simpa using hs_smul_both X Y 1 c


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

/-- PDF p.13, Proposition 20 Eqs.(61)--(63). Eq.(62) constructs normalized representatives;
an arbitrary unit eigenmatrix is one of these up to phase. Eq.(67) instead concerns raw matrices. -/
theorem solution (D : Data G A n) :
    (∀ r : Row D, ∃ p : Fin n × Fin n, 0 < pivotWeight D.U D.F r.1.val r.2 p) ∧
    (∀ r : Row D, ∀ p, 0 < pivotWeight D.U D.F r.1.val r.2 p →
      hs (normalizedMatrix D.U D.F r.1.val r.2 p) (normalizedMatrix D.U D.F r.1.val r.2 p) = 1 ∧
      ∀ s : Row D, fineMap D.U D.F s.1.val s.2 (normalizedMatrix D.U D.F r.1.val r.2 p) =
        if s = r then normalizedMatrix D.U D.F r.1.val r.2 p else 0) ∧
    (∀ r s : Row D, ∀ p q,
      0 < pivotWeight D.U D.F r.1.val r.2 p → 0 < pivotWeight D.U D.F s.1.val s.2 q →
      ∃ zeta : ℝ, hs (normalizedMatrix D.U D.F r.1.val r.2 p)
        (normalizedMatrix D.U D.F s.1.val s.2 q) = if r = s then phase zeta else 0) ∧
    (∀ r : Row D, ∀ X : Mat n, hs X X = 1 → fineMap D.U D.F r.1.val r.2 X = X →
      ∃ p : Fin n × Fin n, 0 < pivotWeight D.U D.F r.1.val r.2 p ∧
        ∃ zeta : ℝ, X = phase zeta • normalizedMatrix D.U D.F r.1.val r.2 p) := by
  refine ⟨positive_pivot D,?_,?_,?_⟩
  · intro r p hp
    exact ⟨normalized_inner_self D r p hp,fun s => normalized_fixed D r s p⟩
  · intro r s p q hp hq
    by_cases hrs : r = s
    · subst s
      obtain ⟨t,ht⟩ := unit_fixed_phase D r _ _ (normalized_inner_self D r p hp)
        (normalized_inner_self D r q hq) (by simpa using normalized_fixed D r r p)
        (by simpa using normalized_fixed D r r q)
      refine ⟨t,?_⟩
      rw [ht,hs_smul_right,normalized_inner_self D r p hp,mul_one,if_pos rfl]
    · refine ⟨0,?_⟩
      simp only [normalizedMatrix,hs_smul_both,raw_inner,if_neg hrs,mul_zero]
  · intro r X hX hfX
    obtain ⟨p,hp⟩ := positive_pivot D r
    refine ⟨p,hp,?_⟩
    exact unit_fixed_phase D r _ X (normalized_inner_self D r p hp) hX
      (by simpa using normalized_fixed D r r p) hfX
