-- Prove2me | solution 1 for QECCertificates.LRAT.prodClauses_three_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:56.367105+00:00
-- url     : https://prove2.me/submissions/15d8e869-2a82-46f8-8ca2-993047d16ad4

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
theorem _root_.solution {τ : Assign} {a x w : Nat}
    (h : τ a = (τ x && τ w)) :
    ∀ C ∈ ([[(a, false), (x, true)], [(a, false), (w, true)],
            [(a, true), (x, false), (w, false)]] : CNF), SatClause τ C := by
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl <;>
    simp only [SatClause, List.mem_cons, List.not_mem_nil, or_false] <;>
    (cases hx : τ x <;> cases hw : τ w <;> simp_all)
end QECCertificates.LRAT
