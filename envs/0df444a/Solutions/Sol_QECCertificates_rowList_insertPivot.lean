-- Prove2me | solution 1 for QECCertificates.rowList_insertPivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:48.802293+00:00
-- url     : https://prove2.me/submissions/59a9dc0f-c0f4-4b9e-8118-51e77d628a94

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivot D w p) = (rowList D).map (fun r => r + (r p) • w) ++ [w] := by
  simp [rowList, insertPivot, List.map_map, Function.comp_def]
end QECCertificates
