-- Prove2me | solution 1 for QECCertificates.Matrix.row_mem_rowSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:02.779728+00:00
-- url     : https://prove2.me/submissions/602083b7-9428-4dec-9e15-c357134f2287

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
namespace Matrix
theorem _root_.solution {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M i ∈ M.certificateRowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)
end Matrix
end QECCertificates
