-- Prove2me | solution 1 for QECCertificates.hgpHZ_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:52.64523+00:00
-- url     : https://prove2.me/submissions/cb5a93ab-40e2-46fe-8cda-c70558df1901

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (ab : Fin n₁ × Fin n₂) :
    hgpHZ H₁ H₂ x (Sum.inl ab) = (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2 := rfl
end QECCertificates
