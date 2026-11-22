-- Prove2me | solution 1 for QECCertificates.inSpanB_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:35.261017+00:00
-- url     : https://prove2.me/submissions/0180c913-6576-4c21-a517-3fabf80ac076

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Theorems.Thm_QECCertificates_inSpanB_iff

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) (v : Vec n) :
    inSpanB L v = false ↔ v ∉ spanL L := by
  constructor
  · intro h hv
    rw [(inSpanB_iff L v).mpr hv] at h
    exact absurd h (by decide)
  · intro h
    cases hb : inSpanB L v with
    | false => rfl
    | true => exact absurd ((inSpanB_iff L v).mp hb) h
end QECCertificates
