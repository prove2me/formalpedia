-- Prove2me | solution 1 for QECCertificates.LRAT.xorChainAux_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:28.23495+00:00
-- url     : https://prove2.me/submissions/2ddc2f84-c69d-4f44-8a46-956556d0a0d4

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
theorem _root_.solution : ∀ (rest : List Nat) (want : Bool) (cur c : Nat),
    (xorChainAux rest want cur c).2 = c + rest.length := by
  intro rest
  induction rest with
  | nil => intro want cur c; rfl
  | cons x rest ih =>
      intro want cur c
      simp only [xorChainAux, List.length_cons]
      rw [ih]
      omega
end QECCertificates.LRAT
