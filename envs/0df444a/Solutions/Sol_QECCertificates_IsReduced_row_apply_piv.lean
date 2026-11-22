-- Prove2me | solution 1 for QECCertificates.IsReduced.row_apply_piv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:21.50381+00:00
-- url     : https://prove2.me/submissions/329258ab-a1db-4c39-ad13-c0116527731e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace IsReduced
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D)
    {ri rj : PivRow n} (hri : ri ∈ D) (hrj : rj ∈ D) :
    ri.1 rj.2 = if ri = rj then 1 else 0 := by
  by_cases h : ri = rj
  · rw [if_pos h, h]; exact hD.1 rj hrj
  · rw [if_neg h]; exact hD.2 ri hri rj hrj h
end IsReduced
end QECCertificates
