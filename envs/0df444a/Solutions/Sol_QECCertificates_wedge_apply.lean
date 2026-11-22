-- Prove2me | solution 1 for QECCertificates.wedge_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:44:16.470082+00:00
-- url     : https://prove2.me/submissions/cd7b9986-6c2e-4dc2-88e6-71ac18d118bc

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (X : VMat p s)
    (k : Fin a) (j : Fin s) : wedge L X (k, j) = L (colOf X j) k := rfl
end QECCertificates
