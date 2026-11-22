-- Prove2me | solution 1 for QECCertificates.lp2HZ_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:19.218995+00:00
-- url     : https://prove2.me/submissions/02fd3e36-bdd9-4487-bdf1-9382144851df

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inr τ) = leftMulMat a τ σ := rfl
end QECCertificates
