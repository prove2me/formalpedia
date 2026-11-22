-- Prove2me | solution 1 for QECCertificates.LRAT.rowFill_prev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:05.219997+00:00
-- url     : https://prove2.me/submissions/50a9a96b-3ade-4434-9ac9-8d393657cac1

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_slotBase_pred
public import Theorems.Thm_QECCertificates_LRAT_rowFill_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {τ : Assign} {c k i cnt j : Nat} (hi : 1 ≤ i)
    (hj : j < min (i - 1) (k + 1)) :
    rowFill τ c k i cnt (c + slotBase k (i - 1) + j) = τ (c + slotBase k (i - 1) + j) := by
  refine rowFill_of_notMem ?_
  rintro ⟨h1, h2⟩
  rw [slotBase_pred hi] at h1
  omega
end QECCertificates.LRAT
