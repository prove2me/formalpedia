-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.fine_sector_unit_vectors_phase
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:07:08.477661+00:00
-- url     : https://prove2.me/submissions/0b51894d-96a2-42e7-9c73-990f91cc805d

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
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
private lemma hs_smul_both (X Y : Mat n) (c d : ℂ) : hs (c • X) (d • Y) = conj c * d * hs X Y := by
  simp [hs_coordinates,map_smul,map_mul,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]
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

theorem solution {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) (r : Row D) (X Y : Mat n)
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