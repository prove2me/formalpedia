-- Prove2me | solution 1 for QECCertificates.lpHZ_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:46.245641+00:00
-- url     : https://prove2.me/submissions/a37f9c15-2881-4880-b0d3-98c9632c1be4

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
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ A B x (Sum.inr y)
      = lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0) := rfl
end QECCertificates
