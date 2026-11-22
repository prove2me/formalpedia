-- Prove2me | solution 1 for QECCertificates.lpHX_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:35.928135+00:00
-- url     : https://prove2.me/submissions/0b6537e3-1164-46f8-90a1-5222cce171a6

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
theorem _root_.solution {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX A B x (Sum.inl y)
      = lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0) := rfl
end QECCertificates
