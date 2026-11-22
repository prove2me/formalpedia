-- Prove2me | solution 1 for QECCertificates.LRAT.dotS_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:16.268795+00:00
-- url     : https://prove2.me/submissions/1b7467a7-5f12-42fa-89d1-94f62d4cc24d

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ τ : Assign} {l : List Nat} (h : ∀ j ∈ l, σ j = τ j) :
    dotS σ l = dotS τ l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      have hj : σ j = τ j := h j (List.mem_cons_self ..)
      have hl : ∀ t ∈ l, σ t = τ t := fun t ht => h t (List.mem_cons_of_mem _ ht)
      simp only [dotS_cons, hj, ih hl]
end QECCertificates.LRAT
