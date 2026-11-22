-- Prove2me | solution 1 for QECCertificates.LRAT.SlotOK.some_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:40.195079+00:00
-- url     : https://prove2.me/submissions/59d71ffc-0dc4-4346-866e-3c90db42aa76

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
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) : ∃ v, s i j = some v := by
  have hne : s i j ≠ none := fun h => (hok i j).mp h ⟨h1, h2⟩
  cases h : s i j with
  | none => exact absurd h hne
  | some v => exact ⟨v, rfl⟩
end SlotOK
end QECCertificates.LRAT
