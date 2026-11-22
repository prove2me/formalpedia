-- Prove2me | solution 1 for QECCertificates.lp2_qubit_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:47.463397+00:00
-- url     : https://prove2.me/submissions/4a96fb4e-46eb-4294-98b9-bf67130997a7

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
theorem _root_.solution [Fintype G] : Fintype.card (G ⊕ G) = 2 * Fintype.card G := by
  rw [Fintype.card_sum]
  ring
end QECCertificates
