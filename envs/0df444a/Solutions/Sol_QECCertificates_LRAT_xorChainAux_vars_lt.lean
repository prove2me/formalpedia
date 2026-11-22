-- Prove2me | solution 1 for QECCertificates.LRAT.xorChainAux_vars_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:14.574422+00:00
-- url     : https://prove2.me/submissions/0b78ca72-b8bf-4c94-8029-c8e58c34e2de

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_xorStepClauses_vars
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
theorem _root_.solution : ∀ (rest : List Nat) (want : Bool) (cur c : Nat),
    cur < c → (∀ t ∈ rest, t < c) →
    ∀ C ∈ (xorChainAux rest want cur c).1, ∀ l ∈ C, l.1 < c + rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c hcur _ C hC l hl
      simp only [xorChainAux, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl
      simpa using hcur
  | cons x rest ih =>
      intro want cur c hcur hrest C hC l hl
      have hx : x < c := hrest x (List.mem_cons_self ..)
      have hrest' : ∀ t ∈ rest, t < c + 1 := fun t ht => by
        have := hrest t (List.mem_cons_of_mem _ ht); omega
      simp only [xorChainAux, List.mem_append] at hC
      simp only [List.length_cons]
      rcases hC with hC | hC
      · rcases xorStepClauses_vars hC l hl with h | h | h <;> omega
      · have h2 := ih want c (c + 1) (by omega) hrest' C hC l hl
        omega
end QECCertificates.LRAT
