-- Prove2me | solution 1 for QECCertificates.LRAT.support_vecOf_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:27.547789+00:00
-- url     : https://prove2.me/submissions/4cc715aa-9826-4e3c-b087-506bfaf991d9

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
public import Theorems.Thm_QECCertificates_LRAT_vecOf_apply_ne_zero
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil
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
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (n : ℕ) :
    (support (vecOf σ n)).card = cntS σ (List.range n) := by
  have h1 : (support (vecOf σ n)).card
      = ∑ t ∈ Finset.range n, if σ t = true then (1 : ℕ) else 0 := by
    rw [support, Finset.card_filter]
    have h : (∑ i : Fin n, if vecOf σ n i ≠ 0 then (1 : ℕ) else 0)
        = ∑ i : Fin n, if σ i.val = true then (1 : ℕ) else 0 :=
      Finset.sum_congr rfl fun i _ => by
        by_cases hv : vecOf σ n i ≠ 0
        · have ht : σ i.val = true := vecOf_apply_ne_zero.mp hv
          simp [hv, ht]
        · have ht : ¬ (σ i.val = true) := fun hc => hv (vecOf_apply_ne_zero.mpr hc)
          simp [hv, ht]
    rw [h]
    exact Fin.sum_univ_eq_sum_range (fun t => if σ t = true then (1 : ℕ) else 0) n
  have h2 : cntS σ (List.range n)
      = ∑ t ∈ Finset.range n, if σ t = true then (1 : ℕ) else 0 := by
    unfold cntS
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter σ List.nodup_range),
      List.toFinset_filter, List.toFinset_range]
    exact Finset.card_filter (fun t => σ t = true) (Finset.range n)
  rw [h1, h2]
end QECCertificates.LRAT
