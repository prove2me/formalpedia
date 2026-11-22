-- Prove2me | solution 1 for QECCertificates.lpHZ_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:42.077816+00:00
-- url     : https://prove2.me/submissions/03199ab2-1650-4904-b8f0-c63c2e1dbfae

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
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ A B x (Sum.inl y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2) := rfl
end QECCertificates
