-- Prove2me | solution 1 for QECCertificates.LRAT.slotBase_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:11.791431+00:00
-- url     : https://prove2.me/submissions/639974e2-badf-42bc-80cc-97bde41a2ea1

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_slotBase_succ

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (k : Nat) {i i' : Nat} (h : i ≤ i') : slotBase k i ≤ slotBase k i' := by
  induction i', h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih => rw [slotBase_succ]; exact le_trans ih (Nat.le_add_right _ _)
end QECCertificates.LRAT
