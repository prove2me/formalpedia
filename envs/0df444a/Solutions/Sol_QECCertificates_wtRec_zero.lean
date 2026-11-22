-- Prove2me | solution 1 for QECCertificates.wtRec_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:02.2408+00:00
-- url     : https://prove2.me/submissions/bfad084c-c347-45e7-8ed8-892c720e6108

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec 0) : wtRec 0 v = 0 := by rw [wtRec.eq_1]
end QECCertificates
