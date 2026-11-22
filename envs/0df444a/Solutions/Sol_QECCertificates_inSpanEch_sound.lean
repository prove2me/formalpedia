-- Prove2me | solution 1 for QECCertificates.inSpanEch_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:56.459655+00:00
-- url     : https://prove2.me/submissions/b6698c78-f644-4435-8d0b-115bc2266185

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_spanL_rowList_echelonFrom
public import Theorems.Thm_QECCertificates_add_reduceAgainst_mem


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {v : Vec n} (h : inSpanEch L v = true) :
    v ∈ spanL L := by
  unfold inSpanEch at h
  rw [decide_eq_true_eq] at h
  have hmem : v + reduceAgainst (echelonFrom L) v ∈ spanL (rowList (echelonFrom L)) :=
    add_reduceAgainst_mem (echelonFrom L) v
  rw [h, add_zero] at hmem
  rwa [spanL_rowList_echelonFrom] at hmem
end QECCertificates
