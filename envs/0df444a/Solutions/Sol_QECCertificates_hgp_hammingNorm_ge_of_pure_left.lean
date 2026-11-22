-- Prove2me | solution 1 for QECCertificates.hgp_hammingNorm_ge_of_pure_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:04.322792+00:00
-- url     : https://prove2.me/submissions/78cbb9e3-8914-48cf-9559-e92cbdaf7aab

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
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hR : blockR v = 0) {d : ℕ}
    (hd : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d ≤ hammingNorm w)
    (hL : blockL v ≠ 0) : d ≤ hammingNorm v := by
  have hcomp : H₁ * blockL v = 0 := by
    have h := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
    rw [hR, Matrix.zero_mul] at h
    exact h
  obtain ⟨a, b, hab⟩ : ∃ a b, blockL v a b ≠ 0 := by
    by_contra hcon
    exact hL (funext fun a => funext fun b => by
      by_contra hc
      exact hcon ⟨a, b, hc⟩)
  have hcol : H₁ *ᵥ (fun a' => blockL v a' b) = 0 := by
    funext a'
    have h2 : (H₁ * blockL v) a' b = 0 := by rw [hcomp]; rfl
    rw [Matrix.mulVec, dotProduct, ← Matrix.mul_apply]
    exact h2
  have hcolne : (fun a' => blockL v a' b) ≠ 0 :=
    fun h => hab (by simpa using congrFun h a)
  calc d ≤ hammingNorm (fun a' => blockL v a' b) := hd _ hcolne hcol
    _ ≤ hammingNorm (fun p : Fin n₁ × Fin n₂ => blockL v p.1 p.2) :=
        hammingNorm_le_of_injective (fun a' : Fin n₁ => (a', b))
          (fun _ _ h => congrArg Prod.fst h) (fun p : Fin n₁ × Fin n₂ => blockL v p.1 p.2)
    _ ≤ hammingNorm v :=
        hammingNorm_le_of_injective (fun p : Fin n₁ × Fin n₂ => Sum.inl p)
          Sum.inl_injective v
end QECCertificates
