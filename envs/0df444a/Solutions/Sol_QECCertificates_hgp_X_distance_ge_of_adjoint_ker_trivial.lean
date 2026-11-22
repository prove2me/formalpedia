-- Prove2me | solution 1 for QECCertificates.hgp_X_distance_ge_of_adjoint_ker_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:59.936376+00:00
-- url     : https://prove2.me/submissions/80fb1544-36dc-4cdd-9c9e-d5a74c929b67

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_blockR_cols_mem_of_adjoint_ker_trivial
public import Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_colClean_free

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v :=
  hgp_X_distance_ge_of_colClean_free H₁ H₂ hv hlog hd₁ fun t =>
    blockR_cols_mem_of_adjoint_ker_trivial (H₁ := H₁) hT t
end QECCertificates
