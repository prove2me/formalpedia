-- Prove2me | solution 1 for QMCLeafB_exists_slack_engine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:24:56.740002+00:00
-- url     : https://prove2.me/submissions/3d26da93-e3c5-460a-9dc0-eab2d2806ce3

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer
import Definitions.Def_QMCLeafB_Rq
import Definitions.Def_QMCLeafB_wMatrixQ

open scoped BigOperators

theorem solution : ∃ eng : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε (QuantumMaxCutEnergy.weightMatrix G) t (1/40000) (1/40000), True := by
  refine ⟨fun G t => ?_, trivial⟩
  classical
  by_cases h : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ, ∃ (_ : QMCLeafB.AnswerProducer.IsUnitDiagPSD X), (QuantumMaxCutEnergy.weightMatrix G * X).trace ≤ (t : ℝ) + ((1/40000 : ℚ) : ℝ)
  · let X := Classical.choose h
    have hX : ∃ (_ : QMCLeafB.AnswerProducer.IsUnitDiagPSD X), (QuantumMaxCutEnergy.weightMatrix G * X).trace ≤ (t : ℝ) + ((1/40000 : ℚ) : ℝ) := Classical.choose_spec h
    let hPSD : QMCLeafB.AnswerProducer.IsUnitDiagPSD X := Classical.choose hX
    have htr : (QuantumMaxCutEnergy.weightMatrix G * X).trace ≤ (t : ℝ) + ((1/40000 : ℚ) : ℝ) := Classical.choose_spec hX
    exact QMCLeafB.AnswerProducer.Answerε.witness X hPSD htr
  · push_neg at h
    refine QMCLeafB.AnswerProducer.Answerε.refuted fun Z hZ => ?_
    have hZ' := h Z hZ
    linarith
