-- Prove2me | solution 1 for QECCertificates.finrank_spanL_eq_length_echelonFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:52.002038+00:00
-- url     : https://prove2.me/submissions/ddcc13c3-b4fe-4253-a466-0652cc182d14

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_spanL_rowList_echelonFrom
public import Theorems.Thm_QECCertificates_linearIndependent_get_of_echelon
public import Theorems.Thm_QECCertificates_echelonFrom_ech
public import Theorems.Thm_QECCertificates_range_get_eq_rowList


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (echelonFrom L).length := by
  have h := echelonFrom_ech L
  have hcard := finrank_span_eq_card (linearIndependent_get_of_echelon h.1 h.2)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList (echelonFrom L)))
      = Fintype.card (Fin (echelonFrom L).length) := hcard
  rw [Fintype.card_fin] at hcard'
  rw [← spanL_rowList_echelonFrom L]
  exact hcard'
end QECCertificates
