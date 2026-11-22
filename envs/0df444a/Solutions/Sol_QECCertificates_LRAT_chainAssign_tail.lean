-- Prove2me | solution 1 for QECCertificates.LRAT.chainAssign_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:11.358245+00:00
-- url     : https://prove2.me/submissions/561fee21-c4ef-411d-b28d-f109b6735cfe

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_succ
public import Theorems.Thm_QECCertificates_LRAT_chainFill_congr
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_of_lt
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_self
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
theorem _root_.solution (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat)
    (hrest : ∀ t ∈ rest, t < c) :
    ∀ t, chainAssign (chainAssign σ (x :: rest) acc c) rest
          (chainAssign σ (x :: rest) acc c c) (c + 1) t
        = chainAssign σ (x :: rest) acc c t := by
  intro t
  by_cases ht : t < c + 1
  · rw [chainAssign_of_lt ht]
  · have ht1 : ¬ t < c + 1 := ht
    have htc : ¬ t < c := by omega
    have hne : t ≠ c := by omega
    simp only [chainAssign, ht1, htc, ite_false]
    rw [chainFill_succ σ x rest acc c t hne]
    exact chainFill_congr rest (chainAssign σ (x :: rest) acc c c) (acc ^^ σ x) (c + 1)
      (chainAssign_self σ x rest acc c)
      (fun t' ht' => chainAssign_of_lt (hrest t' ht')) t
end QECCertificates.LRAT
