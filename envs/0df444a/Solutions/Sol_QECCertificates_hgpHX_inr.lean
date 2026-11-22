-- Prove2me | solution 1 for QECCertificates.hgpHX_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:49.898472+00:00
-- url     : https://prove2.me/submissions/06a905a7-ee32-480d-8378-7de636005419

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
    (x : Fin r₁ × Fin n₂) (st : Fin r₁ × Fin r₂) :
    hgpHX H₁ H₂ x (Sum.inr st) = (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2 := rfl
end QECCertificates
