-- Prove2me | solution 1 for QECCertificates.rankEchelon_eq_length_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:50.123837+00:00
-- url     : https://prove2.me/submissions/9889a49a-b2d7-41b2-b810-dbbcd6956af3

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_finrank_spanL_eq_length_echelonFrom
public import Theorems.Thm_QECCertificates_finrank_spanL_eq_length_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) :
    rankEchelon L = (rowReduce L).length := by
  rw [rankEchelon, ← finrank_spanL_eq_length_rowReduce L,
    finrank_spanL_eq_length_echelonFrom L]
end QECCertificates
