-- Prove2me | solution 1 for QECCertificates.hgp_X_distance_ge_of_H2Ker_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:53.241383+00:00
-- url     : https://prove2.me/submissions/4d0122c4-385d-4f76-9af9-93fc99f69251

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_blockL_rows_mem_of_H2Ker_trivial
public import Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_rowClean_free

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
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) :
    d₂T ≤ hammingNorm v :=
  hgp_X_distance_ge_of_rowClean_free H₁ H₂ hv hlog hd₂ fun a =>
    blockL_rows_mem_of_H2Ker_trivial (H₂ := H₂) hT a
end QECCertificates
