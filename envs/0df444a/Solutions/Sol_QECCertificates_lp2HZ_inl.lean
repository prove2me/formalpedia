-- Prove2me | solution 1 for QECCertificates.lp2HZ_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:14.092407+00:00
-- url     : https://prove2.me/submissions/2c42a5ff-3817-469d-8701-5dc86958d3f5

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
    lp2HZ a b σ (Sum.inl τ) = rightMulMat b τ σ := rfl
end QECCertificates
