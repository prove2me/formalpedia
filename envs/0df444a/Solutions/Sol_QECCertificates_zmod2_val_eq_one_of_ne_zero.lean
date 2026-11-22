-- Prove2me | solution 1 for QECCertificates.zmod2_val_eq_one_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:49.409956+00:00
-- url     : https://prove2.me/submissions/d50a951e-7937-4d6b-b25d-3f251b8a8e62

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
theorem _root_.solution (a : ZMod 2) (ha : a ≠ 0) : a.1 = 1 := by
  have hlt : a.1 < 2 := a.2
  have hne : a.1 ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
  omega
end QECCertificates
