-- Prove2me | solution 1 for QECCertificates.LRAT.buildPair_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:38.948632+00:00
-- url     : https://prove2.me/submissions/18bf7c96-c386-4f85-983f-6bf9cce4e771

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_P2M_QECCertificates_LRAT_xorChain_sat__ae6782a94c56
public import Theorems.Thm_QECCertificates_LRAT_atMostK_sat
public import Theorems.Thm_QECCertificates_LRAT_satFormula_append
public import Theorems.Thm_QECCertificates_LRAT_SatFormula_forall
public import Theorems.Thm_QECCertificates_LRAT_dotS_map
public import Theorems.Thm_QECCertificates_LRAT_dotS_congr
public import Theorems.Thm_QECCertificates_LRAT_prodClauses_sat
public import Theorems.Thm_QECCertificates_LRAT_chainsFrom_sat
public import Theorems.Thm_QECCertificates_LRAT_slotVar_ok
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (h : SatFormula σ (buildPair Rker Rpair n k)) :
    cntS σ (List.range n) ≤ k ∧
    (∀ r ∈ Rker, dotS σ r = false) ∧
    (∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false) ∧
    dotS (fun t => σ t && σ (n + t)) (List.range n) = true := by
  unfold buildPair at h
  obtain ⟨hHead, hE⟩ := satFormula_append.mp h
  obtain ⟨hAB, hCD⟩ := satFormula_append.mp hHead
  obtain ⟨hA, hB⟩ := satFormula_append.mp hAB
  obtain ⟨hC, hD⟩ := satFormula_append.mp hCD
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact atMostK_sat (s := slotVar (c3Of Rker Rpair n) k) (slotVar_ok _ k)
      (SatFormula.forall hE)
  · unfold kerClauses at hA
    exact chainsFrom_sat hne₁ (2 * n) (SatFormula.forall hA)
  · unfold pairClauses at hB
    exact chainsFrom_sat hne₂ (c1Of Rker n) (SatFormula.forall hB)
  · -- `x·w = 1`
    unfold xwClauses at hD
    have hne_prod : prodVars Rker Rpair n ≠ [] := by
      intro h0
      have hlen := congrArg List.length h0
      simp [prodVars, List.length_map, List.length_range] at hlen
      omega
    have hxw : dotS σ (prodVars Rker Rpair n) = true :=
      xorChain_sat' hne_prod (SatFormula.forall hD)
    rw [prodVars, dotS_map] at hxw
    rw [← hxw]
    apply dotS_congr
    intro j hj
    exact (prodClauses_sat (SatFormula.forall hC) j (List.mem_range.mp hj)).symm
end QECCertificates.LRAT
