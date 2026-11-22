-- Prove2me | solution 1 for QECCertificates.inSpanEch_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:04.579385+00:00
-- url     : https://prove2.me/submissions/71320a66-fb20-4b1f-8449-64ba6ffb3763

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_inSpanEch_iff

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = false ↔ v ∉ spanL L := by
  constructor
  · intro h hv
    rw [(inSpanEch_iff L v).mpr hv] at h
    exact absurd h (by decide)
  · intro h
    cases hb : inSpanEch L v with
    | false => rfl
    | true => exact absurd ((inSpanEch_iff L v).mp hb) h
end QECCertificates
