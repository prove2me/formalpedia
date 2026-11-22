-- Prove2me | solution 1 for QECCertificates.LRAT.chainsFrom_snd_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:54.849865+00:00
-- url     : https://prove2.me/submissions/da931971-24bc-45ed-be9e-5b51e11972b5

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_xorChain_snd_ge
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
theorem _root_.solution {f : Nat → Nat} : ∀ (rows : List (List Nat)) (c : Nat),
    c ≤ (chainsFrom f rows c).2 := by
  intro rows
  induction rows with
  | nil => intro c; simp [chainsFrom]
  | cons r₀ rest ih =>
      intro c
      have h := ih ((xorChain (r₀.map f) false c).2)
      have h2 := xorChain_snd_ge (r₀.map f) false c
      simp only [chainsFrom]
      omega
end QECCertificates.LRAT
