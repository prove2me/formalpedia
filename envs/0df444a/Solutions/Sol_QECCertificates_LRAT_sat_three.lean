-- Prove2me | solution 1 for QECCertificates.LRAT.sat_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:42.286407+00:00
-- url     : https://prove2.me/submissions/630e8157-d554-479b-bca2-f77457458d3b

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
theorem _root_.solution {σ : Assign} {a b c : Lit} (h : SatClause σ [a, b, c]) :
    σ a.1 = a.2 ∨ σ b.1 = b.2 ∨ σ c.1 = c.2 := by
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr hv)
end QECCertificates.LRAT
