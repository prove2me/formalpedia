-- Prove2me | solution 1 for QECCertificates.ker_dotProduct_rowSpace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:26.18197+00:00
-- url     : https://prove2.me/submissions/2f6161d3-deaf-4304-a045-c221085a2406

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
public import Theorems.Thm_QECCertificates_mem_ker_iff_dotProd_rows_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
theorem _root_.solution {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (x : Fin n → ZMod 2)
    (hy : y ∈ LinearMap.ker M.toLin') (hx : x ∈ M.certificateRowSpace) : y ⬝ᵥ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [dotProduct_comm]
      exact (mem_ker_iff_dotProd_rows_eq_zero M y).mp hy i
  | zero => simp
  | add a b ha hb iha ihb => rw [dotProduct_add, iha, ihb, add_zero]
  | smul c a ha iha => rw [dotProduct_smul, iha, smul_zero]
end QECCertificates
