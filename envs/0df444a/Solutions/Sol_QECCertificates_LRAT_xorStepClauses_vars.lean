-- Prove2me | solution 1 for QECCertificates.LRAT.xorStepClauses_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:50.673176+00:00
-- url     : https://prove2.me/submissions/06458428-22dd-4a98-9849-fc66f485a1ee

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
theorem _root_.solution {cur x nxt : Nat} {C : Clause}
    (hC : C ∈ xorStepClauses cur x nxt) :
    ∀ l ∈ C, l.1 = cur ∨ l.1 = x ∨ l.1 = nxt := by
  simp only [xorStepClauses, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    (intro l hl
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
     rcases hl with rfl | rfl | rfl <;> simp)
end QECCertificates.LRAT
