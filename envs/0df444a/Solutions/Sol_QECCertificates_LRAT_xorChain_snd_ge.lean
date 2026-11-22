-- Prove2me | solution 1 for QECCertificates.LRAT.xorChain_snd_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:10.339839+00:00
-- url     : https://prove2.me/submissions/067253bf-4188-4a92-9440-c5b399c91de0

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_snd
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
theorem _root_.solution (xs : List Nat) (w : Bool) (c : Nat) :
    c ≤ (xorChain xs w c).2 := by
  cases xs with
  | nil => simp [xorChain]
  | cons x₀ t =>
      have h := xorChainAux_snd t w x₀ c
      simp only [xorChain, h]
      omega
end QECCertificates.LRAT
