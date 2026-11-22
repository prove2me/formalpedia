-- Prove2me | solution 1 for QECCertificates.hgp_X_distance_ge_of_H2TKer_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:57.207643+00:00
-- url     : https://prove2.me/submissions/7744a2ae-bd50-4494-a15e-0b62a4356c14

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_blockR_cols_mem_of_H2TKer_trivial
public import Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_colClean_free
public import Theorems.Thm_QECCertificates_hgpHX_mulVec_eq_zero_iff


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
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v :=
  hgp_X_distance_ge_of_colClean_free H₁ H₂ hv hlog hd₁ fun t =>
    blockR_cols_mem_of_H2TKer_trivial (H₁ := H₁) (H₂ := H₂)
      ((hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv) hT t
end QECCertificates
