-- Prove2me | solution 1 for QECCertificates.hgpHX_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:35.127808+00:00
-- url     : https://prove2.me/submissions/eb89fb12-04cf-41d3-bce7-0d83edb2ef05

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
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (i : Fin r₁) (j : Fin n₂) :
    (hgpHX H₁ H₂ *ᵥ v) (i, j) = (H₁ * blockL v) i j + (blockR v * H₂) i j := by
  have hL : (hgpHX H₁ H₂ *ᵥ v) (i, j)
      = (∑ ab : Fin n₁ × Fin n₂, (H₁ i ab.1 * (if j = ab.2 then 1 else 0)) * v (Sum.inl ab))
      + (∑ st : Fin r₁ × Fin r₂, ((if i = st.1 then 1 else 0) * H₂ st.2 j) * v (Sum.inr st)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    congr 1
  have hR1 : (H₁ * blockL v) i j = ∑ a, H₁ i a * v (Sum.inl (a, j)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [blockL_apply]
  have hR2 : (blockR v * H₂) i j = ∑ t, H₂ t j * v (Sum.inr (i, t)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [blockR_apply, mul_comm]
  rw [hL, hR1, hR2,
    sum_prod_slice_snd (A := fun a => H₁ i a) (F := fun a b => v (Sum.inl (a, b))) j,
    sum_prod_slice_fst (B := fun t => H₂ t j) (F := fun s t => v (Sum.inr (s, t))) i]
end QECCertificates
