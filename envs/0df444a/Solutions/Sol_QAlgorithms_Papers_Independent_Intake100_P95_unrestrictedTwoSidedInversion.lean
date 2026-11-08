-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P95.unrestrictedTwoSidedInversion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:27:11.781066+00:00
-- url     : https://prove2.me/submissions/dad5750b-32a5-4172-80d4-99c2bbef11cd

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

open scoped BigOperators

noncomputable section

theorem solution {n : ℕ} (hn : 0 < n)
    (U : Matrix.specialUnitaryGroup (QAlgorithms.Qubits n) ℂ) :
    (U⁻¹ * U⁻¹) * U * 1 = U⁻¹ ∧
    ∃ U1 U2 : Matrix.specialUnitaryGroup (QAlgorithms.Qubits n) ℂ,
      U1 * U * U2 = U⁻¹ := by
  refine ⟨by group, U⁻¹, U⁻¹, by group⟩
