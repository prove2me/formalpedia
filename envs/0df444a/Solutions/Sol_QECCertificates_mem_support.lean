-- Prove2me | solution 1 for QECCertificates.mem_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:04.761702+00:00
-- url     : https://prove2.me/submissions/db1d29bb-bfa0-44ca-b320-65d3a9097c7c

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {v : Vec n} {i : Fin n} : i ∈ support v ↔ v i ≠ 0 := by
  simp [support]
end QECCertificates
