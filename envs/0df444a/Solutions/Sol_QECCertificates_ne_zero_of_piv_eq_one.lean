-- Prove2me | solution 1 for QECCertificates.ne_zero_of_piv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:19.375568+00:00
-- url     : https://prove2.me/submissions/daa37d0c-3130-443d-889a-aee6329556bd

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {v : Vec n} {p : Fin n} (h : v p = 1) : v ≠ 0 :=
  fun hzero => by rw [hzero, Pi.zero_apply] at h; exact one_ne_zero h.symm
end QECCertificates
