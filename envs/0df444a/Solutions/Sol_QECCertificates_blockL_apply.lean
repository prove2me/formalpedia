-- Prove2me | solution 1 for QECCertificates.blockL_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:42.518799+00:00
-- url     : https://prove2.me/submissions/41dcc7e0-b26a-455d-a3db-d34e58db3891

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (a : Fin n₁) (b : Fin n₂) : blockL v a b = v (Sum.inl (a, b)) := rfl
end QECCertificates
