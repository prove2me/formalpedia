-- Prove2me | solution 1 for QECCertificates.exists_mulVec_of_mem_spanL_colList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:10.565532+00:00
-- url     : https://prove2.me/submissions/a0498f1c-6c25-4d93-89b3-90de53e11493

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
    {y : Vec m} (h : y ∈ spanL (colList M)) : ∃ x : Vec k, M *ᵥ x = y := by
  have h' : y ∈ Submodule.span (ZMod 2) {v : Vec m | v ∈ colList M} := h
  refine Submodule.span_induction (p := fun v _ => ∃ x : Vec k, M *ᵥ x = v)
    ?_ ?_ ?_ ?_ h'
  · intro v hv
    obtain ⟨i, hi⟩ := mem_matRowList.mp hv
    refine ⟨unitVec i, ?_⟩
    funext j
    rw [← congrFun hi j]
    rw [Matrix.mulVec, dotProduct]
    have hsum : (∑ b, M j b * unitVec i b) = M j i := by
      rw [Finset.sum_eq_single i]
      · rw [unitVec, if_pos rfl, mul_one]
      · intro b _ hb
        rw [unitVec, if_neg (fun h : b = i => hb h), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum]
    exact (Matrix.transpose_apply M i j).symm
  · exact ⟨0, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [Matrix.mulVec_add, ha, hb]⟩
  · intro c x _ hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by rw [Matrix.mulVec_smul, ha]⟩
end QECCertificates
