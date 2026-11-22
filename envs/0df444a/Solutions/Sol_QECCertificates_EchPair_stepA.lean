-- Prove2me | solution 1 for QECCertificates.EchPair_stepA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:39.398655+00:00
-- url     : https://prove2.me/submissions/9cb7ec93-ce84-4672-8ddc-61d2943b6821

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_reduceAgainst_get_piv_eq_zero
public import Theorems.Thm_QECCertificates_EchPair_append

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) (v : Vec n) :
    EchPair (stepA D v) := by
  unfold stepA
  split
  · exact h2
  · rename_i hw
    exact EchPair_append D _ h2 fun i => reduceAgainst_get_piv_eq_zero v h1 h2 i
end QECCertificates
