-- Prove2me | solution 1 for QECCertificates.dual_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:26.742831+00:00
-- url     : https://prove2.me/submissions/73bbc687-5a84-4f65-9141-52fcbcce4e5c

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
theorem _root_.solution {n : ℕ} (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
  convert f.pi_apply_eq_sum_univ v using 1
  simp only [dotProduct, smul_eq_mul, mul_comm]
  exact Finset.sum_congr rfl fun i _ => by congr; ext j; aesop
end QECCertificates
