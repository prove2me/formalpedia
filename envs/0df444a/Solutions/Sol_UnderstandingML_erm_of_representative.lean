-- Prove2me | solution 1 for UnderstandingML.erm_of_representative
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T12:52:47.759072+00:00
-- url     : https://prove2.me/submissions/a7364235-baf3-4464-9320-8f3371f12460

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

theorem solution {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (D : Measure Z) {ε : ℝ} {m : ℕ} (S : Fin m → Z)
    (hS : IsRepresentative loss H D (ε / 2) S) (h : Hyp) (hERM : IsERM loss H S h) :
    ∀ h' ∈ H, risk loss D h ≤ risk loss D h' + ε := by
  intro h' hh'
  have h1 := abs_le.mp (hS h hERM.1)
  have h2 := abs_le.mp (hS h' hh')
  have h3 := hERM.2 h' hh'
  linarith [h1.1, h2.2]
