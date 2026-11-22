-- Prove2me | solution 1 for QECCertificates.wtRec_eq_hammingNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:00.631014+00:00
-- url     : https://prove2.me/submissions/ad6e4f50-8e3c-45d6-b947-07698837a8dc

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Theorems.Thm_QECCertificates_wtRec_eq_card_support
public import Theorems.Thm_QECCertificates_weight_eq_hammingNorm


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec n) : wtRec n v = hammingNorm v := by
  rw [wtRec_eq_card_support, weight_eq_hammingNorm]
end QECCertificates
