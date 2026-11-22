-- Prove2me | solution 1 for QECCertificates.LRAT.dotS_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:31.085666+00:00
-- url     : https://prove2.me/submissions/673a06c7-c8f6-4c03-9434-e749eefa7044

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (s t : List Nat) :
    dotS σ (s ++ t) = (dotS σ s ^^ dotS σ t) := by
  induction s with
  | nil => simp
  | cons j s ih => simp only [List.cons_append, dotS_cons, ih]; rw [Bool.xor_assoc]
end QECCertificates.LRAT
