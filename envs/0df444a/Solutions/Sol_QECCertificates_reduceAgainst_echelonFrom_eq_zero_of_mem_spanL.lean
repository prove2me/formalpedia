-- Prove2me | solution 1 for QECCertificates.reduceAgainst_echelonFrom_eq_zero_of_mem_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:54.665828+00:00
-- url     : https://prove2.me/submissions/88b2590d-4a15-45c0-9cdd-7b58fe1e9587

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_spanL_rowList_echelonFrom
public import Theorems.Thm_QECCertificates_reduceAgainst_get_piv_eq_zero
public import Theorems.Thm_QECCertificates_echelonFrom_ech
public import Theorems.Thm_QECCertificates_eq_zero_of_mem_spanL_of_piv_eq_zero
public import Theorems.Thm_QECCertificates_add_add_same_right
public import Theorems.Thm_QECCertificates_add_reduceAgainst_mem


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {v : Vec n}
    (hv : v ∈ spanL L) : reduceAgainst (echelonFrom L) v = 0 := by
  have hech := echelonFrom_ech L
  have hmem : v + reduceAgainst (echelonFrom L) v ∈ spanL L := by
    have h := add_reduceAgainst_mem (echelonFrom L) v
    rwa [spanL_rowList_echelonFrom] at h
  refine eq_zero_of_mem_spanL_of_piv_eq_zero hech.1 hech.2 ?_
    (reduceAgainst_get_piv_eq_zero v hech.1 hech.2)
  rw [spanL_rowList_echelonFrom]
  have hsplit : (v + reduceAgainst (echelonFrom L) v) + v
      = reduceAgainst (echelonFrom L) v := by
    rw [add_assoc, add_add_same_right]
  rw [← hsplit]
  exact Submodule.add_mem _ hmem hv
end QECCertificates
