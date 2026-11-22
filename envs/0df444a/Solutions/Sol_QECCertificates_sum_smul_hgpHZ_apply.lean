-- Prove2me | solution 1 for QECCertificates.sum_smul_hgpHZ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:17.551053+00:00
-- url     : https://prove2.me/submissions/4c76ec84-065a-4284-a61e-983dd2151436

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hgpHZ_inl
public import Theorems.Thm_QECCertificates_hgpHZ_inr
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.readOff_nil
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (C : Matrix (Fin n₁) (Fin r₂) (ZMod 2))
    (c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) :
    (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p) c
      = Sum.elim (fun ab => (C * H₂) ab.1 ab.2) (fun st => (H₁ * C) st.1 st.2) c := by
  rw [Finset.sum_apply]
  rcases c with ab | st
  · obtain ⟨a, b⟩ := ab
    simp only [Pi.smul_apply, smul_eq_mul, hgpHZ_inl]
    change (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 * ((if p.1 = a then 1 else 0) * H₂ p.2 b))
      = (C * H₂) a b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hstep : ∀ a' : Fin n₁, (∑ d, C a' d * ((if a' = a then 1 else 0) * H₂ d b))
        = (if a' = a then 1 else 0) * (∑ d, C a' d * H₂ d b) := by
      intro a'
      have hterm : ∀ d : Fin r₂, C a' d * ((if a' = a then 1 else 0) * H₂ d b)
          = (if a' = a then 1 else 0) * (C a' d * H₂ d b) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a' _ => hstep a']
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, one_mul]
    · intro a' _ ha'
      rw [if_neg (fun h : a' = a => ha' h), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · obtain ⟨s, t⟩ := st
    simp only [Pi.smul_apply, smul_eq_mul, hgpHZ_inr]
    change (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 * (H₁ s p.1 * (if p.2 = t then 1 else 0)))
      = (H₁ * C) s t
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hstep : ∀ a' : Fin n₁, (∑ d, C a' d * (H₁ s a' * (if d = t then 1 else 0)))
        = H₁ s a' * C a' t := by
      intro a'
      have hterm : ∀ d : Fin r₂, C a' d * (H₁ s a' * (if d = t then 1 else 0))
          = H₁ s a' * (C a' d * (if d = t then 1 else 0)) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => hterm d]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_eq_single t]
      · rw [if_pos rfl, mul_one]
      · intro d _ hd
        rw [if_neg (fun h : d = t => hd h), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ t) h
    rw [Finset.sum_congr rfl fun a' _ => hstep a']
end QECCertificates
