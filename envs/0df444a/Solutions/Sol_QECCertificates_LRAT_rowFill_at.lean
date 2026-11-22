-- Prove2me | solution 1 for QECCertificates.LRAT.rowFill_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:00.294469+00:00
-- url     : https://prove2.me/submissions/c2691b35-7a50-4ddb-8e2e-ebfe9671806c

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
theorem _root_.solution {τ : Assign} {c k i cnt j : Nat} (hj : j < min i (k + 1)) :
    rowFill τ c k i cnt (c + slotBase k i + j) = decide (j + 1 ≤ cnt) := by
  have hsub : c + slotBase k i + j - (c + slotBase k i) = j := by omega
  simp only [rowFill, hsub]
  rw [if_pos (by omega : c + slotBase k i ≤ c + slotBase k i + j ∧
    c + slotBase k i + j < c + slotBase k i + min i (k + 1))]
end QECCertificates.LRAT
