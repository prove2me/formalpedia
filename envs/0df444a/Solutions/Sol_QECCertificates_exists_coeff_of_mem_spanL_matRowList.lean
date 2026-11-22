-- Prove2me | solution 1 for QECCertificates.exists_coeff_of_mem_spanL_matRowList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:12.499929+00:00
-- url     : https://prove2.me/submissions/afe1415a-2ad7-4c43-aae4-066b3b456da3

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_mem_matRowList
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
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
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∈ spanL (matRowList M)) :
    ∃ co : Vec m, ∀ j, (∑ t, co t * M t j) = y j := by
  have h' : y ∈ Submodule.span (ZMod 2) {v : Vec k | v ∈ matRowList M} := h
  refine Submodule.span_induction
    (p := fun v _ => ∃ co : Vec m, ∀ j, (∑ t, co t * M t j) = v j) ?_ ?_ ?_ ?_ h'
  · intro v hv
    obtain ⟨i, hi⟩ := mem_matRowList.mp hv
    refine ⟨unitVec i, fun j => ?_⟩
    rw [← hi]
    have hsum : (∑ t, unitVec i t * M t j) = M i j := by
      rw [Finset.sum_eq_single i]
      · rw [unitVec, if_pos rfl, one_mul]
      · intro b _ hb
        rw [unitVec, if_neg (fun h : b = i => hb h), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum]
  · exact ⟨0, fun j => by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, fun j => ?_⟩
    change (∑ t, (a + b) t * M t j) = x j + y j
    rw [← ha j, ← hb j]
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.add_apply, add_mul]
  · intro c x _ hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨c • a, fun j => ?_⟩
    change (∑ t, (c • a) t * M t j) = c • (x j)
    rw [← ha j, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
end QECCertificates
