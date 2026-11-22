-- Prove2me | solution 1 for QECCertificates.lp2HX_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:46.619127+00:00
-- url     : https://prove2.me/submissions/dd48c629-1b6a-4396-ad15-68449e50281f

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
    lp2HX a b σ (Sum.inl τ) = leftMulMat a σ τ := rfl
end QECCertificates
