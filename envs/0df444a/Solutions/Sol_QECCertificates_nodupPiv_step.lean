-- Prove2me | solution 1 for QECCertificates.nodupPiv_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:47.242858+00:00
-- url     : https://prove2.me/submissions/e0314058-fae7-42db-a602-f40f74250602

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodupPiv_insertPivot
public import Theorems.Thm_QECCertificates_leadIdx_eq_one
public import Theorems.Thm_QECCertificates_reduceAgainst_apply_piv


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hred : IsReduced D) (hD : NodupPiv D) (v : Vec n) :
    NodupPiv (step D v) := by
  unfold step
  split
  · exact hD
  · rename_i hw
    refine nodupPiv_insertPivot hD ?_
    intro hmem
    obtain ⟨ri, hri, hri2⟩ := List.mem_map.mp hmem
    have h1 : reduceAgainst D v ri.2 = 0 := reduceAgainst_apply_piv hred v ri hri
    rw [hri2, leadIdx_eq_one (reduceAgainst D v) hw] at h1
    exact one_ne_zero h1
end QECCertificates
