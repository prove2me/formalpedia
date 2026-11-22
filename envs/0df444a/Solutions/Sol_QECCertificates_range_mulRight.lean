-- Prove2me | solution 1 for QECCertificates.range_mulRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:05.628989+00:00
-- url     : https://prove2.me/submissions/f27ef35c-9096-43b4-9859-eb354cbd643f

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
theorem _root_.solution (B : Matrix (Fin r) (Fin s) (ZMod 2)) :
    LinearMap.range (mulRight (p := p) B) = rowsSub (Matrix.certificateRowSpace B) := by
  ext X
  constructor
  · rintro ⟨N, rfl⟩ i
    have hrow : rowOf (mulRight B N) i = ∑ t, N (i, t) • (fun j => B t j) := by
      funext j
      simp only [rowOf_apply, mulRight, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    rw [hrow]
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro hX
    choose f hf using fun i => (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)
      (v := B) (x := rowOf X i)).mp (hX i)
    refine ⟨fun it => f it.1 it.2, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    have hstep : ∑ t, f i t * B t j = X (i, j) := by
      have h := congrFun (hf i) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply] at h
      exact h
    exact hstep
end QECCertificates
