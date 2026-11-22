-- Prove2me | solution 1 for QECCertificates.LRAT.prodFill_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:47.444972+00:00
-- url     : https://prove2.me/submissions/a4663575-c7b1-45f7-9692-f9c068d59bba

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {c n t : Nat} (h : t < c) :
    prodFill σ c n t = σ t := by
  simp only [prodFill]
  rw [if_neg (by omega : ¬ (c ≤ t ∧ t < c + n))]
end QECCertificates.LRAT
