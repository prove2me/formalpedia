-- Prove2me | solution 1 for QECCertificates.LRAT.prodClauses_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:21.067707+00:00
-- url     : https://prove2.me/submissions/c23ba0da-a3ca-4cd5-abac-37d0ce8b7f76

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_prodFill_at
public import Theorems.Thm_QECCertificates_LRAT_prodClauses_three_sat
public import Theorems.Thm_QECCertificates_LRAT_prodFill_of_lt
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
theorem _root_.solution {c n : Nat} {σ : Assign} (hc : 2 * n ≤ c) :
    ∀ C ∈ prodClauses c n, SatClause (prodFill σ c n) C := by
  intro C hC
  simp only [prodClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨j, hj, hCj⟩ := hC
  refine prodClauses_three_sat ?_ C hCj
  rw [prodFill_at σ c n j hj,
    show prodFill σ c n j = σ j from prodFill_of_lt (by omega),
    show prodFill σ c n (n + j) = σ (n + j) from prodFill_of_lt (by omega)]
end QECCertificates.LRAT
