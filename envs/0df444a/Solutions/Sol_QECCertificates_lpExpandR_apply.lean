-- Prove2me | solution 1 for QECCertificates.lpExpandR_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:25.250073+00:00
-- url     : https://prove2.me/submissions/450ade77-1f0b-4d7c-83d8-f1c9f43a03d8

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
theorem _root_.solution {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (i : Fin mA) (σ : G) (j : Fin nA) (τ : G) :
    lpExpandR A (i, σ) (j, τ) = leftMulMat (A i j) σ τ := rfl
end QECCertificates
