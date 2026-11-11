-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:21:08.282483+00:00
-- url     : https://prove2.me/submissions/5940735e-41c8-4b1a-8889-83f1007e9af7

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
import Definitions.Def_QMCTied_Final
open scoped BigOperators

theorem solution
    (k : ℕ) (hk : 2 ≤ k) (ε : ℚ≥0) (hε : 0 < ε) :
    ∃ B : QuantumMaxCutEnergy.Algorithm,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun req : QuantumMaxCutEnergy.Input × List Bool => (B.run req.1 req.2 : ℚ))) ∧
      B.randomFactor = 0 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (B.run G [] : ℝ) ≤ QuantumMaxCutEnergy.PauliSDP.value k G ∧
        QuantumMaxCutEnergy.PauliSDP.value k G -
          (ε : ℝ) * (∑ e, (G.weights e : ℝ)) ≤ (B.run G [] : ℝ) :=
  QMCTied.pauli_value_compiler k hk ε hε
