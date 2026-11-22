-- Prove2me | solution 1 for QECCertificates.LRAT.SlotOK.none_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:40.674808+00:00
-- url     : https://prove2.me/submissions/23b53098-6026-4f49-a8b0-fd6af2112122

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
namespace SlotOK
theorem _root_.solution {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h : ¬(1 ≤ j ∧ j ≤ min i (k + 1))) : s i j = none := (hok i j).mpr h
end SlotOK
end QECCertificates.LRAT
