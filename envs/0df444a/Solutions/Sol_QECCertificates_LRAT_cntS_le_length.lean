-- Prove2me | solution 1 for QECCertificates.LRAT.cntS_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:58.655726+00:00
-- url     : https://prove2.me/submissions/0acee1b9-342c-47ba-b3ec-f9a0c442fb4d

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (l : List Nat) : cntS σ l ≤ l.length :=
  List.length_filter_le _ _
end QECCertificates.LRAT
