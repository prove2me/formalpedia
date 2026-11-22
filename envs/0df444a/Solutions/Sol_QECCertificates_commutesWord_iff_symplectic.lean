-- Prove2me | solution 1 for QECCertificates.commutesWord_iff_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:32.421317+00:00
-- url     : https://prove2.me/submissions/4af20c1a-d56f-412b-83b6-74ab4d84acbe

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
public import Theorems.Thm_QECCertificates_Pauli_anti_eq_symp

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (u v : PauliWord n) :
    commutesWord u v ↔
      (sympWord u).1 ⬝ᵥ (sympWord v).2 + (sympWord v).1 ⬝ᵥ (sympWord u).2 = 0 := by
  rw [commutesWord]
  have hcongr : ∑ i, Pauli.anti (u i) (v i)
      = ∑ i, ((sympWord u).1 i * (sympWord v).2 i + (sympWord v).1 i * (sympWord u).2 i) :=
    Finset.sum_congr rfl fun i _ => Pauli.anti_eq_symp (u i) (v i)
  rw [hcongr, Finset.sum_add_distrib]
  rw [show (∑ i, (sympWord u).1 i * (sympWord v).2 i)
        = (sympWord u).1 ⬝ᵥ (sympWord v).2 from rfl,
      show (∑ i, (sympWord v).1 i * (sympWord u).2 i)
        = (sympWord v).1 ⬝ᵥ (sympWord u).2 from rfl]
end QECCertificates
