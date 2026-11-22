-- Prove2me | solution 1 for QECCertificates.lpHX_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:39.170709+00:00
-- url     : https://prove2.me/submissions/1366bb04-7d5d-48a6-b8c1-608055bbf8a2

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
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX A B x (Sum.inr y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2) := rfl
end QECCertificates
