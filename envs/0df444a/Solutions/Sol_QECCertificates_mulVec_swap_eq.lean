-- Prove2me | solution 1 for QECCertificates.mulVec_swap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:08.108316+00:00
-- url     : https://prove2.me/submissions/28f16cce-9609-43ea-af3e-0f2a9382d7ff

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Theorems.Thm_QECCertificates_swapBlocks_swapBlocks
public import Theorems.Thm_QECCertificates_swapBlocks_injective
public import Theorems.Thm_QECCertificates_hgpHZ_row_eq_swap

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
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (x : Fin n₁ × Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) x
      = (hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c))) x := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  have h₁ : (∑ c, hgpHZ H₁ H₂ x c * v c)
      = ∑ c, hgpHX H₁.transpose H₂.transpose x (swapBlocks c) * v c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [congrFun (hgpHZ_row_eq_swap H₁ H₂ x) c]
  rw [h₁]
  refine Finset.sum_bij (fun c _ => swapBlocks c) ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro c _ c' _ h; exact swapBlocks_injective h
  · intro c' _; exact ⟨swapBlocks c', Finset.mem_univ _, swapBlocks_swapBlocks c'⟩
  · intro c _
    rw [swapBlocks_swapBlocks]
end QECCertificates
