-- Prove2me | solution 1 for QECCertificates.hgpHZ_mulVec_eq_zero_iff_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:42.743422+00:00
-- url     : https://prove2.me/submissions/61b86293-05fb-4064-bed8-cc186ee8f15b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Theorems.Thm_QECCertificates_mulVec_swap_eq

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔
      hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c)) = 0 := by
  constructor <;> intro h
  · funext x
    rw [← mulVec_swap_eq H₁ H₂ v x, congrFun h x]
  · funext x
    rw [mulVec_swap_eq H₁ H₂ v x, congrFun h x]
end QECCertificates
