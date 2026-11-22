-- Prove2me | solution 1 for QECCertificates.LRAT.xorChain_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:40.336848+00:00
-- url     : https://prove2.me/submissions/cf0acb00-9d0d-4f11-ab45-35ec58fd8192

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_sat

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {x₀ : Nat} {rest : List Nat} {want : Bool} {start : Nat}
    (h : ∀ C ∈ (xorChainAux rest want x₀ start).1, SatClause σ C) :
    dotS σ (x₀ :: rest) = want :=
  xorChainAux_sat rest want x₀ start σ h
end QECCertificates.LRAT
