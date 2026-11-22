-- Prove2me | solution 1 for QECCertificates.LRAT.satClause_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:40.799335+00:00
-- url     : https://prove2.me/submissions/9fd90b04-a4ac-481b-85fa-53e80b05042c

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ τ : Assign} {C : Clause} {c : Nat}
    (h : ∀ t, t < c → τ t = σ t) (hvars : ∀ l ∈ C, l.1 < c) (hC : SatClause σ C) :
    SatClause τ C := by
  obtain ⟨l, hl, hv⟩ := hC
  exact ⟨l, hl, by rw [h l.1 (hvars l hl), hv]⟩
end QECCertificates.LRAT
