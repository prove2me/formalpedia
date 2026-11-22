-- Prove2me | solution 1 for QECCertificates.LRAT.slotVar_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:18.007243+00:00
-- url     : https://prove2.me/submissions/4ec50dfa-0e79-4333-a557-1eb2c0c9c4d0

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {c k i j : Nat} (h : ¬ (1 ≤ j ∧ j ≤ min i (k + 1))) :
    slotVar c k i j = none := by
  rw [slotVar, if_neg h]
end QECCertificates.LRAT
