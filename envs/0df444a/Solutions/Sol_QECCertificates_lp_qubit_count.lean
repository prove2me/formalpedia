-- Prove2me | solution 1 for QECCertificates.lp_qubit_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:33.590445+00:00
-- url     : https://prove2.me/submissions/8483d419-1fd2-457b-b013-58dbfa3b0fb5

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
theorem _root_.solution [Fintype G] {mA nA mB nB : ℕ} :
    Fintype.card (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G))
      = (nA * mB + mA * nB) * Fintype.card G := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  ring
end QECCertificates
