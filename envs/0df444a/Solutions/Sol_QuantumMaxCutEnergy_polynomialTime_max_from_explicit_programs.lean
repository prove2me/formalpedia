-- Prove2me | solution 1 for QuantumMaxCutEnergy.polynomialTime_max_from_explicit_programs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:42:16.318757+00:00
-- url     : https://prove2.me/submissions/6d28f273-2821-4ad7-882c-7599bd4f37fe

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

theorem solution
    (A : QuantumMaxCutEnergy.Algorithm) (b : QuantumMaxCutEnergy.Input → ℚ≥0)
    (Pb : OAI.MetricKMedian.Binary.PolyProgram
      QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
      (fun req : QuantumMaxCutEnergy.Input × List Bool => (b req.1 : ℚ)))
    (PA : OAI.MetricKMedian.Binary.PolyProgram
      QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
      (fun req : QuantumMaxCutEnergy.Input × List Bool => (A.run req.1 req.2 : ℚ))) :
    QuantumMaxCutEnergy.PolynomialTime
      { randomFactor := A.randomFactor
        randomDegree := A.randomDegree
        run := fun G r => max (b G) (A.run G r) } := by
  exact QMCNumericRuntime.EstimatorComposition.withFloor_polynomialTime A b Pb PA
#print axioms solution
