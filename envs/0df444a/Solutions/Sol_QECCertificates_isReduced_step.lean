-- Prove2me | solution 1 for QECCertificates.isReduced_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:18.469476+00:00
-- url     : https://prove2.me/submissions/8afffb0c-4bd3-47e9-b97d-14e0b146ab98

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_reduceAgainst_apply_piv
public import Theorems.Thm_QECCertificates_leadIdx_eq_one
public import Theorems.Thm_QECCertificates_isReduced_insertPivot

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    IsReduced (step D v) := by
  unfold step
  split
  · exact hD
  · rename_i hw
    exact isReduced_insertPivot hD (leadIdx_eq_one (reduceAgainst D v) hw)
      (reduceAgainst_apply_piv hD v)
end QECCertificates
