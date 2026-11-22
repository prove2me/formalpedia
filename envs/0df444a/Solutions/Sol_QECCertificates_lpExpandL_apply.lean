-- Prove2me | solution 1 for QECCertificates.lpExpandL_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:28.039226+00:00
-- url     : https://prove2.me/submissions/25e5a99c-4bb2-48d1-a524-ce5de88e5a99

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
theorem _root_.solution {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (s : Fin mB) (σ : G) (t : Fin nB) (τ : G) :
    lpExpandL B (s, σ) (t, τ) = rightMulMat (B s t) σ τ := rfl
end QECCertificates
