-- Prove2me | solution 1 for QECCertificates.not_mem_rowspace_iff_exists_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:38.070201+00:00
-- url     : https://prove2.me/submissions/ea5fddfa-74b7-474e-8497-0c75bee522dc

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
public import Theorems.Thm_QECCertificates_ker_dotProduct_rowSpace_eq_zero
public import Theorems.Thm_QECCertificates_exists_ker_dotProduct_eq_one_of_not_mem_rowSpace

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
theorem _root_.solution {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin
    n → (ZMod 2)) :
  x ∉ M.certificateRowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by
  constructor
  · exact exists_ker_dotProduct_eq_one_of_not_mem_rowSpace M x
  · rintro ⟨y, hy_ker, hy_dot⟩ hx
    have := ker_dotProduct_rowSpace_eq_zero M y x hy_ker hx
    simp_all
end QECCertificates
