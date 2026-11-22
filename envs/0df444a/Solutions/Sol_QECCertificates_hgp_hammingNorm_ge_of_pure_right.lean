-- Prove2me | solution 1 for QECCertificates.hgp_hammingNorm_ge_of_pure_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:09.745504+00:00
-- url     : https://prove2.me/submissions/cbea7dfb-2d3a-452a-a2d7-db22e61c0f8f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hgpHX_mulVec_eq_zero_iff
public import Theorems.Thm_QECCertificates_hammingNorm_le_of_injective
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hL : blockL v = 0) {d : ℕ}
    (hd : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d ≤ hammingNorm w)
    (hR : blockR v ≠ 0) : d ≤ hammingNorm v := by
  have hcomp : blockR v * H₂ = 0 := by
    have h := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
    rw [hL, Matrix.mul_zero] at h
    exact h.symm
  obtain ⟨s, t, hst⟩ : ∃ s t, blockR v s t ≠ 0 := by
    by_contra hcon
    exact hR (funext fun s => funext fun t => by
      by_contra hc
      exact hcon ⟨s, t, hc⟩)
  have hrow : H₂.transpose *ᵥ (fun t' => blockR v s t') = 0 := by
    funext t'
    have h2 : (blockR v * H₂) s t' = 0 := by rw [hcomp]; rfl
    have h3 : (H₂.transpose *ᵥ (fun t' => blockR v s t')) t' = (blockR v * H₂) s t' := by
      rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun t _ => by rw [Matrix.transpose_apply, mul_comm]
    rw [h3]
    exact h2
  have hrowne : (fun t' => blockR v s t') ≠ 0 :=
    fun h => hst (by simpa using congrFun h t)
  calc d ≤ hammingNorm (fun t' => blockR v s t') := hd _ hrowne hrow
    _ ≤ hammingNorm (fun q : Fin r₁ × Fin r₂ => blockR v q.1 q.2) :=
        hammingNorm_le_of_injective (fun t' : Fin r₂ => (s, t'))
          (fun _ _ h => congrArg Prod.snd h) (fun q : Fin r₁ × Fin r₂ => blockR v q.1 q.2)
    _ ≤ hammingNorm v :=
        hammingNorm_le_of_injective (fun q : Fin r₁ × Fin r₂ => Sum.inr q)
          Sum.inr_injective v
end QECCertificates
