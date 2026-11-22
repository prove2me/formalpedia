-- Prove2me | solution 1 for QECCertificates.lowerHyp_of_lightCand_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:50.097172+00:00
-- url     : https://prove2.me/submissions/e69a7fa7-547d-42d1-b3c6-370069ce6160

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_mem_lightCand
public import Theorems.Thm_QECCertificates_Matrix_rowSpace_eq_spanL_ofFn
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_castSuccEmb_apply
public import Theorems.Thm_QECCertificates_inKerB_iff
public import Theorems.Thm_QECCertificates_inSpanEch_eq_false_iff
public import Theorems.Thm_QECCertificates_lightVecs_nil
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_lightVecs
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_snocV_castSucc
public import Theorems.Thm_QECCertificates_snocV_last
public import Theorems.Thm_QECCertificates_snocV_zero_zero
public import Theorems.Thm_QECCertificates_wtRec_eq_hammingNorm
public import Theorems.Thm_QECCertificates_wtRec_zero
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.castSuccEmb_apply
attribute [local simp] QECCertificates.lightVecs_nil
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil
attribute [local simp] QECCertificates.snocV_castSucc
attribute [local simp] QECCertificates.snocV_last
attribute [local simp] QECCertificates.snocV_zero_zero
attribute [local simp] QECCertificates.wtRec_zero



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : lightCand M₁ M₂ d = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.certificateRowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lightCand M₁ M₂ d := by
    rw [mem_lightCand]
    exact ⟨hcov, hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanEch_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem
end QECCertificates
