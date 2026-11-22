-- Prove2me | solution 1 for QECCertificates.EchSelf_stepA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:28.131796+00:00
-- url     : https://prove2.me/submissions/8acbf471-8f83-4e4a-ad08-a6a01bf9bfef

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_EchSelf_append
public import Theorems.Thm_QECCertificates_leadIdx_eq_one


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (h1 : EchSelf D) (v : Vec n) :
    EchSelf (stepA D v) := by
  unfold stepA
  split
  · exact h1
  · rename_i hw
    exact EchSelf_append D _ h1 (leadIdx_eq_one (reduceAgainst D v) hw)
end QECCertificates
