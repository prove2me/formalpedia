-- Prove2me | solution 1 for QECCertificates.echSelf_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:15.547562+00:00
-- url     : https://prove2.me/submissions/840a97bb-11d1-4662-8386-a2ef2bd512f0

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution : EchSelf ([] : List (PivRow n)) := by intro i; exact i.elim0
end QECCertificates
