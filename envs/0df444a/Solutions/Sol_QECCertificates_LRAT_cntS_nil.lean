-- Prove2me | solution 1 for QECCertificates.LRAT.cntS_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:07.749618+00:00
-- url     : https://prove2.me/submissions/c2d3ff51-07b3-4e3c-9b1c-c9cb2dc132cb

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) : cntS σ [] = 0 := rfl
end QECCertificates.LRAT
