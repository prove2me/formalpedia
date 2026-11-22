-- Prove2me | solution 1 for QECCertificates.exists_row_of_exists_mem_rowspace_non_orth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:21.944814+00:00
-- url     : https://prove2.me/submissions/fcdf2b86-e654-4521-99b6-2c1228166ed5

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Theorems.Thm_QECCertificates_exists_dotProduct_one_of_sum
public import Theorems.Thm_QECCertificates_Matrix_mem_rowSpace_ZMod2

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
theorem _root_.solution {n k : ℕ}
  {M : Matrix (Fin k) (Fin n) (ZMod 2)}
  {x y : Fin n → (ZMod 2)}
  (hy₁ : y ∈ M.certificateRowSpace)
  (hy₂ : y ⬝ᵥ x = 1) :
  ∃ r, (M r) ⬝ᵥ x = 1 := by
  rw [Matrix.mem_rowSpace_ZMod2] at hy₁
  obtain ⟨S, hS_sub, hS_sum⟩ := hy₁
  obtain ⟨s, hs_mem, hs_dot⟩ := exists_dotProduct_one_of_sum hS_sum hy₂
  obtain ⟨ i, -, hi ⟩ := Finset.mem_image.mp (hS_sub hs_mem)
  refine ⟨ i, ?_ ⟩
  rwa [hi]
end QECCertificates
