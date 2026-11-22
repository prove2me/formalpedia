-- Prove2me | solution 1 for QECCertificates.lp_row_count_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:43.501588+00:00
-- url     : https://prove2.me/submissions/69e6a245-3bc5-4610-98e9-41c1623edec6

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
omit [Group G]
namespace QECCertificates
theorem _root_.solution [Fintype G] {nA nB : ℕ} :
    Fintype.card ((Fin nA × Fin nB) × G) = nA * nB * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
end QECCertificates
