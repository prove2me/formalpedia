-- Prove2me | solution 1 for QECCertificates.mem_ker_iff_dotProd_rows_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:19.925509+00:00
-- url     : https://prove2.me/submissions/1904d9b9-61cb-481e-98bd-2286d8ab1588

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

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
theorem _root_.solution {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n
    → (ZMod 2)) :
  x ∈ ((LinearMap.ker M.toLin')) ↔ ∀ i, (M i) ⬝ᵥ x = 0 := by
  constructor
  · intro h i
    simpa [Matrix.mulVec, dotProduct] using congr_fun h i
  · intro h
    ext i
    simpa [Matrix.mulVec, dotProduct] using h i
end QECCertificates
