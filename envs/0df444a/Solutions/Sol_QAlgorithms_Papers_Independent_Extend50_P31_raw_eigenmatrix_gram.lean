-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.raw_eigenmatrix_gram
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:00:27.428159+00:00
-- url     : https://prove2.me/submissions/3c55cc8e-9e9e-4ff5-97ea-0dde4dc0b8f6

import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition17_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary19_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma hs_coordinates (X Y : Mat n) : hs X Y = ∑ p : Fin n × Fin n, conj (rowVec X p) * rowVec Y p := by
  simp [hs,res,PiLp.inner_apply,RCLike.inner_apply,rowVec,mul_comm]
private lemma row_matrixUnit (p : Fin n × Fin n) : rowVec (matrixUnit p.1 p.2) = Pi.single p (1 : ℂ) := by
  ext q
  simp [rowVec,matrixUnit,Matrix.single_apply,Pi.single_apply,Prod.ext_iff,eq_comm]
private lemma raw_coordinates (D : Data G A n) (r : Row D) (p : Fin n × Fin n) :
    rowVec (rawMatrix D.U D.F r.1.val r.2 p) =
      fun q => fineMatrix D.U D.F r.1.val r.2 q p := by
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  change rowVec (fineMap D.U D.F r.1.val r.2 (matrixUnit p.1 p.2)) = _
  rw [ha,(corollary19_refinement D).1 r,row_matrixUnit]
  exact Matrix.mulVec_single_one _ p

set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) (r s : Row D) (p q : Fin n × Fin n) :
    hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F s.1.val s.2 q) =
      if r = s then fineMatrix D.U D.F r.1.val r.2 p q else 0 := by
  rw [hs_coordinates,raw_coordinates,raw_coordinates]
  change ((fineMatrix D.U D.F r.1.val r.2)ᴴ * fineMatrix D.U D.F s.1.val s.2) p q = _
  rw [((proposition17_refinement D).2.2 r).1,(proposition17_refinement D).2.1]
  split_ifs <;> rfl