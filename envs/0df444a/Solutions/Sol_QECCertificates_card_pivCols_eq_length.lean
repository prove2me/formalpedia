-- Prove2me | solution 1 for QECCertificates.card_pivCols_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:20.913458+00:00
-- url     : https://prove2.me/submissions/435614a9-2e04-4355-9c33-9f3a0bf7ddbf

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (h : NodupPiv D) :
    (pivCols D).card = D.length := by
  rw [pivCols, List.toFinset_card_of_nodup h, List.length_map]
end QECCertificates
