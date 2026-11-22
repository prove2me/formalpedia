-- Prove2me | solution 1 for QECCertificates.LRAT.prodClauses_vars_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:08.518801+00:00
-- url     : https://prove2.me/submissions/dfa346fd-416a-420e-a824-832b3a166e8a

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
theorem _root_.solution {c n : Nat} (hc : n ≤ c) :
    ∀ C ∈ prodClauses c n, ∀ l ∈ C, l.1 < c + n := by
  intro C hC l hl
  simp only [prodClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨j, hj, hCj⟩ := hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
  rcases hCj with hCj | hCj | hCj <;> rw [hCj] at hl <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
     rcases hl with rfl | rfl | rfl <;> omega)
end QECCertificates.LRAT
