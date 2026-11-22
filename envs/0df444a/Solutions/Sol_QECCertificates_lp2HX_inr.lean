-- Prove2me | solution 1 for QECCertificates.lp2HX_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:04.062906+00:00
-- url     : https://prove2.me/submissions/79a6e607-4526-4865-9de2-18acf0d4b751

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
    lp2HX a b σ (Sum.inr τ) = rightMulMat b σ τ := rfl
end QECCertificates
