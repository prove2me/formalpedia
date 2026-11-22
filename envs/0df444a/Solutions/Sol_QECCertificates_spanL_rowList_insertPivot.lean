-- Prove2me | solution 1 for QECCertificates.spanL_rowList_insertPivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:26.187782+00:00
-- url     : https://prove2.me/submissions/c2560ab5-340a-49c0-83bb-503cbbca4090

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_rowList_insertPivot
public import Theorems.Thm_QECCertificates_spanL_map_addSmul_append


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    spanL (rowList (insertPivot D w p)) = spanL (rowList D ++ [w]) := by
  rw [rowList_insertPivot]
  exact spanL_map_addSmul_append _ _ _
end QECCertificates
