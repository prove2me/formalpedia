-- Prove2me | solution 1 for QECCertificates.nodupPiv_rowReduceFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:50.504012+00:00
-- url     : https://prove2.me/submissions/0d1d353c-d972-4507-9a96-eeee48dc92b7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodupPiv_step
public import Theorems.Thm_QECCertificates_isReduced_step
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_cons



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (rest : List (Vec n)) :
    IsReduced D → NodupPiv D → NodupPiv (rowReduceFrom D rest) := by
  induction rest generalizing D with
  | nil => intro _ hD; exact hD
  | cons v rest ih =>
      intro hred hD
      rw [rowReduceFrom_cons]
      exact ih (step D v) (isReduced_step hred v) (nodupPiv_step hred hD v)
end QECCertificates
