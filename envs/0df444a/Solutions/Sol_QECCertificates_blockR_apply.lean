-- Prove2me | solution 1 for QECCertificates.blockR_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:43.326338+00:00
-- url     : https://prove2.me/submissions/0fbb1e6a-c495-4a1d-b4af-d1e54c06c70d

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
    (s : Fin r₁) (t : Fin r₂) : blockR v s t = v (Sum.inr (s, t)) := rfl
end QECCertificates
