-- Prove2me | solution 1 for QECCertificates.hgpHZ_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:27.368017+00:00
-- url     : https://prove2.me/submissions/2b384ba0-65d7-431b-8640-85ad1d1defe2

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_sum_prod_slice_snd
public import Theorems.Thm_QECCertificates_sum_prod_slice_fst
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
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (a : Fin n₁) (d : Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) (a, d) = (blockL v * H₂.transpose) a d + (H₁.transpose * blockR v) a d := by
  have hL : (hgpHZ H₁ H₂ *ᵥ v) (a, d)
      = (∑ ab : Fin n₁ × Fin n₂, ((if a = ab.1 then 1 else 0) * H₂ d ab.2) * v (Sum.inl ab))
      + (∑ st : Fin r₁ × Fin r₂, (H₁ st.1 a * (if d = st.2 then 1 else 0)) * v (Sum.inr st)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    congr 1
  have hR1 : (blockL v * H₂.transpose) a d = ∑ b, H₂ d b * v (Sum.inl (a, b)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Matrix.transpose_apply, blockL_apply, mul_comm]
  have hR2 : (H₁.transpose * blockR v) a d = ∑ s, H₁ s a * v (Sum.inr (s, d)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Matrix.transpose_apply, blockR_apply]
  rw [hL, hR1, hR2,
    sum_prod_slice_fst (B := fun b => H₂ d b) (F := fun a b => v (Sum.inl (a, b))) a,
    sum_prod_slice_snd (A := fun s => H₁ s a) (F := fun s t => v (Sum.inr (s, t))) d]
end QECCertificates
