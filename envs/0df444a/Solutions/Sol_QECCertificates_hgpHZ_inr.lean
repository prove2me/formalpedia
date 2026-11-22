-- Prove2me | solution 1 for QECCertificates.hgpHZ_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:54.481419+00:00
-- url     : https://prove2.me/submissions/66e09a78-9fc8-4c21-8f08-3dc0fec35db5

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
    (x : Fin n₁ × Fin r₂) (st : Fin r₁ × Fin r₂) :
    hgpHZ H₁ H₂ x (Sum.inr st) = H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0) := rfl
end QECCertificates
