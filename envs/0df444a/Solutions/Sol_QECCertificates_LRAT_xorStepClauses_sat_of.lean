-- Prove2me | solution 1 for QECCertificates.LRAT.xorStepClauses_sat_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:44.100546+00:00
-- url     : https://prove2.me/submissions/7e16ba32-3f25-4a93-a7e1-750cb66ac018

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
theorem _root_.solution {τ : Assign} {cur x nxt : Nat}
    (h : τ nxt = (τ cur ^^ τ x)) :
    ∀ C ∈ xorStepClauses cur x nxt, SatClause τ C := by
  intro C hC
  simp only [xorStepClauses, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    simp only [SatClause, List.mem_cons, List.not_mem_nil, or_false] <;>
    (cases hv : τ cur <;> cases hw : τ x <;> simp_all)
end QECCertificates.LRAT
