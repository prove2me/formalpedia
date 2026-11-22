-- Prove2me | solution 1 for QECCertificates.LRAT.no_light_logical_of_unsat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:51.848797+00:00
-- url     : https://prove2.me/submissions/30c861b0-59c0-442f-9c6f-8eea2f0558c4

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
public import Theorems.Thm_QECCertificates_LRAT_support_vecOf_card
public import Theorems.Thm_QECCertificates_LRAT_dotS_eq_false_iff_dotProduct
public import Theorems.Thm_QECCertificates_LRAT_zmod2_eq_one_of_ne_zero
public import Theorems.Thm_QECCertificates_LRAT_vecOf_certAssign
public import Theorems.Thm_QECCertificates_LRAT_vecOf_certAssign_shift
public import Theorems.Thm_QECCertificates_LRAT_vecOf_and
public import Theorems.Thm_QECCertificates_LRAT_rowOf_range
public import Theorems.Thm_QECCertificates_LRAT_buildPair_complete
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_Matrix_rowSpace_eq_spanL_ofFn
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_exists_ker_dot_ne_zero_of_not_mem
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_ker_iff_dotProd_rows_eq_zero
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
theorem _root_.solution {n k : ℕ} {Rker Rpair : List (List Nat)}
    {m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {F : CNF}
    (hF : buildPair Rker Rpair n k = F) (hunsat : ¬ Satisfiable F) (hn : 0 < n)
    (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hb₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hb₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hd₁ : ∀ r ∈ Rker, r.Nodup) (hd₂ : ∀ r ∈ Rpair, r.Nodup)
    (hrow₁ : Rker.map (rowOf n) = List.ofFn fun i => M₁ i)
    (hrow₂ : Rpair.map (rowOf n) = List.ofFn fun i => M₂ i) :
    ¬ ∃ E : Vec n, (support E).card ≤ k ∧ E ∈ (Matrix.toLin' M₁).ker
      ∧ E ∉ M₂.certificateRowSpace := by
  rintro ⟨E, hw, hker, hrow⟩
  have hspan : E ∉ spanL (List.ofFn fun i => M₂ i) := by
    rw [← Matrix.rowSpace_eq_spanL_ofFn]
    exact hrow
  obtain ⟨w, hwmv, hwdot⟩ := exists_ker_dot_ne_zero_of_not_mem M₂ hspan
  have hwdot1 : E ⬝ᵥ w = 1 := zmod2_eq_one_of_ne_zero hwdot
  have hrowE : ∀ i, (M₁ i) ⬝ᵥ E = 0 := (mem_ker_iff_dotProd_rows_eq_zero M₁ E).mp hker
  have hmemker : w ∈ (Matrix.toLin' M₂).ker := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact hwmv
  have hroww : ∀ i, (M₂ i) ⬝ᵥ w = 0 := (mem_ker_iff_dotProd_rows_eq_zero M₂ w).mp hmemker
  have hwt : cntS (certAssign n E w) (List.range n) ≤ k := by
    rw [← support_vecOf_card (certAssign n E w) n, vecOf_certAssign E w]
    exact hw
  have hkerS : ∀ r ∈ Rker, dotS (certAssign n E w) r = false := by
    intro r hr
    rw [dotS_eq_false_iff_dotProduct (certAssign n E w) (hb₁ r hr) (hd₁ r hr),
      vecOf_certAssign E w]
    have hmem : rowOf n r ∈ List.ofFn (fun i => M₁ i) := by
      rw [← hrow₁]
      exact List.mem_map_of_mem hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
    rw [← hi]
    exact hrowE i
  have hpairS : ∀ r ∈ Rpair, dotS (fun t => certAssign n E w (n + t)) r = false := by
    intro r hr
    rw [dotS_eq_false_iff_dotProduct (fun t => certAssign n E w (n + t))
      (hb₂ r hr) (hd₂ r hr), vecOf_certAssign_shift E w]
    have hmem : rowOf n r ∈ List.ofFn (fun i => M₂ i) := by
      rw [← hrow₂]
      exact List.mem_map_of_mem hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
    rw [← hi]
    exact hroww i
  have hxwS : dotS (fun t => certAssign n E w t && certAssign n E w (n + t))
      (List.range n) = true := by
    have hne : dotS (fun t => certAssign n E w t && certAssign n E w (n + t))
        (List.range n) ≠ false := by
      intro hf
      have h0 := (dotS_eq_false_iff_dotProduct _
        (fun t ht => List.mem_range.mp ht) List.nodup_range).mp hf
      rw [rowOf_range, vecOf_and, vecOf_certAssign E w, vecOf_certAssign_shift E w,
        dotProduct] at h0
      simp only [one_mul] at h0
      rw [← dotProduct, hwdot1] at h0
      exact one_ne_zero h0
    cases h : dotS (fun t => certAssign n E w t && certAssign n E w (n + t))
        (List.range n) <;> simp_all
  obtain ⟨τ, -, hτ⟩ := buildPair_complete (Rker := Rker) (Rpair := Rpair) (n := n) (k := k)
    (σ := certAssign n E w) hn hne₁ hne₂ hb₁ hb₂ hwt hkerS hpairS hxwS
  exact hunsat ⟨τ, by rwa [hF] at hτ⟩
end QECCertificates.LRAT
