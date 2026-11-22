-- Prove2me | solution 1 for QECCertificates.commutesWord_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:13.47553+00:00
-- url     : https://prove2.me/submissions/a843fd4a-8b40-46df-a07f-f2079203fd21

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
public import Theorems.Thm_QECCertificates_Pauli_anti_comm

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {u v : PauliWord n} (h : commutesWord u v) : commutesWord v u := by
  rw [commutesWord] at h ⊢
  have hswap : (∑ i, Pauli.anti (v i) (u i)) = (∑ i, Pauli.anti (u i) (v i)) :=
    Finset.sum_congr rfl fun i _ => Pauli.anti_comm (v i) (u i)
  rw [hswap]; exact h
end QECCertificates
