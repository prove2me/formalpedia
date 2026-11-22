-- Prove2me | solution 1 for QECCertificates.castSuccEmb_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:38.217639+00:00
-- url     : https://prove2.me/submissions/2dc3f8b1-6ceb-4eae-97dd-8e853720dab7

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
theorem _root_.solution (i : Fin n) : Fin.castSuccEmb i = i.castSucc := rfl
end QECCertificates
