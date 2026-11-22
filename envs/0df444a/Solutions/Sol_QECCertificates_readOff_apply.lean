-- Prove2me | solution 1 for QECCertificates.readOff_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:28.223811+00:00
-- url     : https://prove2.me/submissions/8720d0b0-3a1b-4e0b-a4e5-65ea015d8beb

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
theorem _root_.solution (D : List (PivRow n)) (w : Vec n) (i : Fin n) :
    readOff D w i = ∑ ri ∈ D.toFinset, (w ri.2) * (ri.1 i) := by
  rw [readOff, Finset.sum_apply]
  exact Finset.sum_congr rfl fun ri _ => by rw [Pi.smul_apply, smul_eq_mul]
end QECCertificates
