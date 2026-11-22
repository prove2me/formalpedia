-- Prove2me | solution 1 for QECCertificates.LRAT.SatFormula.forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:45.300441+00:00
-- url     : https://prove2.me/submissions/cd937790-9ce4-4460-be31-fbe8c9a10154

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
namespace SatFormula
theorem _root_.solution {σ : Assign} {F : CNF} (h : SatFormula σ F) :
    ∀ C ∈ F, SatClause σ C := h
end SatFormula
end QECCertificates.LRAT
