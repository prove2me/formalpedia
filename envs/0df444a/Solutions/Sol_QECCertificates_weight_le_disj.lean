-- Prove2me | solution 1 for QECCertificates.weight_le_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:19.207248+00:00
-- url     : https://prove2.me/submissions/f2355b6b-170f-4b42-a4ba-11e19720d0eb

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
theorem _root_.solution {n k : ℕ} {z : Fin n → (ZMod 2)} : hammingNorm z ≤ k ↔ ∑ i, (z i).1 ≤ k := by
  simp +decide only [hammingNorm]
  rw [ Finset.card_filter ]
  exact iff_of_eq ( by congr; ext i; rcases z i with ( _ | _ | i ) <;> trivial )
end QECCertificates
