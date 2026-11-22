-- Prove2me | solution 1 for QECCertificates.LRAT.satFormula_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:22.234664+00:00
-- url     : https://prove2.me/submissions/8d23f4a2-3709-451d-9d5a-ae7f4f6ef5e8

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {A B : CNF} :
    SatFormula σ (A ++ B) ↔ SatFormula σ A ∧ SatFormula σ B := by
  constructor
  · intro h
    exact ⟨fun C hC => h C (List.mem_append_left _ hC),
      fun C hC => h C (List.mem_append_right _ hC)⟩
  · rintro ⟨hA, hB⟩ C hC
    rcases List.mem_append.mp hC with h | h
    · exact hA C h
    · exact hB C h
end QECCertificates.LRAT
