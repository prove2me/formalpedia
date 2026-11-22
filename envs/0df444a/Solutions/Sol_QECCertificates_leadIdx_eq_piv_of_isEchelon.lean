-- Prove2me | solution 1 for QECCertificates.leadIdx_eq_piv_of_isEchelon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:29.232213+00:00
-- url     : https://prove2.me/submissions/3ee68c01-697f-4325-b9e6-db3f172a316f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_leadIdx_le_of_ne_zero
public import Theorems.Thm_QECCertificates_leadIdx_spec


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (h : IsEchelon D) {ri : PivRow n}
    (hri : ri ∈ D) {hne : ri.1 ≠ 0} : leadIdx ri.1 hne = ri.2 := by
  refine le_antisymm ?_ ?_
  · exact leadIdx_le_of_ne_zero hne (by rw [h.1.1 ri hri]; exact one_ne_zero)
  · by_contra hlt
    exact absurd (h.2 ri hri (leadIdx ri.1 hne) (not_le.mp hlt)) (leadIdx_spec ri.1 hne)
end QECCertificates
