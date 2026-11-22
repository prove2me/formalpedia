-- Prove2me | solution 1 for QECCertificates.hgpHX_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:44.91841+00:00
-- url     : https://prove2.me/submissions/b7a04ee5-589f-4af9-a6ec-e4b5df147287

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
    (x : Fin r₁ × Fin n₂) (ab : Fin n₁ × Fin n₂) :
    hgpHX H₁ H₂ x (Sum.inl ab) = H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0) := rfl
end QECCertificates
