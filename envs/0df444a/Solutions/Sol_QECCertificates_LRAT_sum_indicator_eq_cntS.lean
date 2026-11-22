-- Prove2me | solution 1 for QECCertificates.LRAT.sum_indicator_eq_cntS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:39.790704+00:00
-- url     : https://prove2.me/submissions/f49a0ce5-f748-47ea-8006-c63894a6b988

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
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
theorem _root_.solution (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    (∑ i : Fin n, (if (i : ℕ) ∈ r then (if σ i.val then (1 : ZMod 2) else 0) else 0))
      = ((cntS σ r : ℕ) : ZMod 2) := by
  have hcard : {t ∈ r.toFinset | σ t = true}.card = cntS σ r := by
    have h1 : (r.toFinset.filter (fun t => σ t = true)).card
        = (r.filter σ).toFinset.card := by
      rw [List.toFinset_filter]
    have h2 : (r.filter σ).toFinset.card = (r.filter σ).length :=
      List.toFinset_card_of_nodup (List.Nodup.filter σ hrn)
    unfold cntS
    exact h1.trans h2
  simp only [← List.mem_toFinset]
  rw [Fin.sum_univ_eq_sum_range
      (fun t => if t ∈ r.toFinset then (if σ t then (1 : ZMod 2) else 0) else 0) n]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.range n).filter (fun t => t ∈ r.toFinset) = r.toFinset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hr t h, h⟩⟩
  rw [hfilt, Finset.sum_boole, hcard]
end QECCertificates.LRAT
