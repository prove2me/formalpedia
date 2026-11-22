-- Prove2me | solution 1 for QECCertificates.inSpanEch_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:17.39535+00:00
-- url     : https://prove2.me/submissions/98de9975-4edf-419b-a09a-c9e55bee4a8e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_inSpanEch_sound
public import Theorems.Thm_QECCertificates_inSpanEch_complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = true ↔ v ∈ spanL L :=
  ⟨inSpanEch_sound, inSpanEch_complete⟩
end QECCertificates
