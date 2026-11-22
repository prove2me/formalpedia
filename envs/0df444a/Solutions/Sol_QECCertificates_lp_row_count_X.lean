-- Prove2me | solution 1 for QECCertificates.lp_row_count_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:37.541798+00:00
-- url     : https://prove2.me/submissions/7e3ba96f-34c3-462e-9c35-7c56735c6f1a

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
theorem _root_.solution [Fintype G] {mA mB : ℕ} :
    Fintype.card ((Fin mA × Fin mB) × G) = mA * mB * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
end QECCertificates
