-- Prove2me | solution 1 for QECCertificates.LRAT.slotBase_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:54.465591+00:00
-- url     : https://prove2.me/submissions/4f2dce92-cd18-4b86-a98f-cc8ffbce89a8

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_slotBase_succ

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {k i : Nat} (hi : 1 ≤ i) :
    slotBase k i = slotBase k (i - 1) + min (i - 1) (k + 1) := by
  have h := slotBase_succ k (i - 1)
  rwa [show i - 1 + 1 = i from by omega] at h
end QECCertificates.LRAT
