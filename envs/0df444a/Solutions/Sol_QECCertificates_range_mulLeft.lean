-- Prove2me | solution 1 for QECCertificates.range_mulLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:04.75969+00:00
-- url     : https://prove2.me/submissions/0d006b66-696b-40fc-beb9-1c90d9d8f7a2

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_vee_apply
public import Theorems.Thm_QECCertificates_wedge_apply
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil
attribute [local simp] QECCertificates.vee_apply
attribute [local simp] QECCertificates.wedge_apply



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (A : Matrix (Fin p) (Fin q) (ZMod 2)) :
    LinearMap.range (mulLeft (s := s) A) = colsSub (LinearMap.range A.mulVecLin) := by
  ext X
  constructor
  · rintro ⟨M, rfl⟩ j
    refine ⟨colOf M j, ?_⟩
    funext i
    rw [Matrix.mulVecLin_apply]
    simp only [Matrix.mulVec, dotProduct, colOf_apply, mulLeft, LinearMap.coe_mk,
      AddHom.coe_mk]
  · intro hX
    choose f hf using fun j => hX j
    refine ⟨fun aj => f aj.2 aj.1, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    have hstep : ∑ x, A i x * f j x = X (i, j) := by
      have h := congrFun (hf j) i
      rw [Matrix.mulVecLin_apply] at h
      simp only [Matrix.mulVec, dotProduct, colOf_apply] at h
      exact h
    exact hstep
end QECCertificates
