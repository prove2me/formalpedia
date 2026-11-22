-- Prove2me | solution 1 for P2M_QECCertificates_LRAT_xorChain_sat__ae6782a94c56
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:06.711563+00:00
-- url     : https://prove2.me/submissions/7e896c59-602e-4b6e-a2cf-089351439dcc

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_xorChain_sat

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {xs : List Nat} {want : Bool} {start : Nat}
    (hne : xs ≠ []) (h : ∀ C ∈ (xorChain xs want start).1, SatClause σ C) :
    dotS σ xs = want := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ rest => exact xorChain_sat h
end QECCertificates.LRAT
