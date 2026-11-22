-- Prove2me | solution 1 for QECCertificates.eq_zero_of_lt_leadIdx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:26.692189+00:00
-- url     : https://prove2.me/submissions/da878960-ee7b-45ef-b526-71d5040fe50e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_leadIdx_le_of_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {v : Vec n} (h : v ≠ 0) {i : Fin n} (hi : i < leadIdx v h) :
    v i = 0 := by
  by_contra hne
  exact absurd (leadIdx_le_of_ne_zero h hne) (not_le.mpr hi)
end QECCertificates
