-- Prove2me | solution 1 for QECCertificates.LRAT.xorStep_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:36.330918+00:00
-- url     : https://prove2.me/submissions/f113741e-c952-4b69-a4da-49de6b17adb1

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_sat_three
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {cur x nxt : Nat}
    (h : ∀ C ∈ xorStepClauses cur x nxt, SatClause σ C) :
    σ nxt = (σ cur ^^ σ x) := by
  have h1 : SatClause σ [(cur, false), (x, false), (nxt, false)] :=
    h _ (by simp [xorStepClauses])
  have h2 : SatClause σ [(cur, false), (x, true), (nxt, true)] :=
    h _ (by simp [xorStepClauses])
  have h3 : SatClause σ [(cur, true), (x, false), (nxt, true)] :=
    h _ (by simp [xorStepClauses])
  have h4 : SatClause σ [(cur, true), (x, true), (nxt, false)] :=
    h _ (by simp [xorStepClauses])
  have k1 : σ cur = false ∨ σ x = false ∨ σ nxt = false := sat_three h1
  have k2 : σ cur = false ∨ σ x = true ∨ σ nxt = true := sat_three h2
  have k3 : σ cur = true ∨ σ x = false ∨ σ nxt = true := sat_three h3
  have k4 : σ cur = true ∨ σ x = true ∨ σ nxt = false := sat_three h4
  by_cases hc : σ cur = true <;> by_cases hx : σ x = true <;> simp_all
end QECCertificates.LRAT
