-- Prove2me | solution 1 for QECCertificates.length_rowReduce_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:41.624435+00:00
-- url     : https://prove2.me/submissions/5f37b725-cec5-4439-a934-45615114d634

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodupPiv_rowReduce
public import Theorems.Thm_QECCertificates_card_pivCols_eq_length

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) : (rowReduce L).length ≤ n := by
  rw [← card_pivCols_eq_length (nodupPiv_rowReduce L)]
  calc (pivCols (rowReduce L)).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n
end QECCertificates
