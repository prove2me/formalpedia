-- Prove2me | solution 1 for QECCertificates.LRAT.decide_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:24.922842+00:00
-- url     : https://prove2.me/submissions/d8fe5f3f-c0db-4e8f-878c-c4aa598901d3

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
theorem _root_.solution {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    decide P = true → decide Q = true := fun hp => by
  have := h (of_decide_eq_true hp)
  simp only [decide_eq_true_eq]; exact this
end QECCertificates.LRAT
