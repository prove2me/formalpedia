-- Prove2me | solution 1 for QECCertificates.LRAT.dotS_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:06.385594+00:00
-- url     : https://prove2.me/submissions/60bb0455-0701-4837-a937-c1fd9581a6da

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) : dotS σ [] = false := rfl
end QECCertificates.LRAT
