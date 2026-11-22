-- Prove2me | solution 1 for QECCertificates.LRAT.chainAssign_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:54.426081+00:00
-- url     : https://prove2.me/submissions/ab41532b-c55d-4b6a-be7c-af6167f8e293

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_congr
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_of_lt
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
theorem _root_.solution {σ σ' : Assign} {rest : List Nat} {acc acc' : Bool} {c : Nat}
    (hacc : acc = acc') (hlt : ∀ t, t < c → σ t = σ' t) (h : ∀ t ∈ rest, σ t = σ' t) :
    ∀ t, chainAssign σ rest acc c t = chainAssign σ' rest acc' c t := by
  intro t
  by_cases ht : t < c
  · rw [chainAssign_of_lt ht, chainAssign_of_lt ht, hlt t ht]
  · have h1 : ¬ t < c := ht
    simp only [chainAssign, h1, ite_false]
    exact chainFill_congr rest acc acc' c hacc h t
end QECCertificates.LRAT
