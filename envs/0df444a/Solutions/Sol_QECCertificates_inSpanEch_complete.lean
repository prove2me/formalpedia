-- Prove2me | solution 1 for QECCertificates.inSpanEch_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:40.790458+00:00
-- url     : https://prove2.me/submissions/78b46236-63e0-4837-b996-5006f2f13253

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_reduceAgainst_echelonFrom_eq_zero_of_mem_spanL

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanEch L v = true := by
  unfold inSpanEch
  rw [decide_eq_true_eq]
  exact reduceAgainst_echelonFrom_eq_zero_of_mem_spanL hv
end QECCertificates
