-- Prove2me | solution 1 for QECCertificates.LRAT.decide_imp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:56.140049+00:00
-- url     : https://prove2.me/submissions/172733c1-8c4d-4567-a2b4-22c5b0065b4b

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
theorem _root_.solution {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (h : P → Q → R) : decide P = true → decide Q = true → decide R = true := by
  intro hp hq
  have := h (of_decide_eq_true hp) (of_decide_eq_true hq)
  simp only [decide_eq_true_eq]; exact this
end QECCertificates.LRAT
