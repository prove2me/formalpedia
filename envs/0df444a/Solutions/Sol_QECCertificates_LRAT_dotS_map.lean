-- Prove2me | solution 1 for QECCertificates.LRAT.dotS_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:15.815899+00:00
-- url     : https://prove2.me/submissions/de3e2b73-cf69-4929-98fe-1a37274326ea

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    dotS σ (l.map f) = dotS (fun t => σ (f t)) l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.map_cons, dotS_cons, ih]
end QECCertificates.LRAT
