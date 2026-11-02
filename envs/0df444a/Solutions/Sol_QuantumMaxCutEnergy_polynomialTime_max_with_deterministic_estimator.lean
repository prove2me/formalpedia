-- Prove2me | solution 1 for QuantumMaxCutEnergy.polynomialTime_max_with_deterministic_estimator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:50:55.634441+00:00
-- url     : https://prove2.me/submissions/89b99c43-201c-469d-91a6-a675e7c5ae16

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_QuantumMaxCutEnergy_exists_polyProgram_of_tm2InPolyTime
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem solution (P : QuantumMaxCutEnergy.Algorithm) (b : QuantumMaxCutEnergy.Input → ℚ≥0)
    (hP : QuantumMaxCutEnergy.PolynomialTime P)
    (hb : Nonempty (Turing.TM2ComputableInPolyTime
      QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => b request.1))) :
    QuantumMaxCutEnergy.PolynomialTime
      { randomFactor := P.randomFactor
        randomDegree := P.randomDegree
        run := fun G r => max (b G) (P.run G r) } := by
  obtain ⟨hb'⟩ := hb
  obtain ⟨hP'⟩ := hP
  obtain ⟨Pb⟩ := QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime
    QuantumMaxCutEnergy.encodeRequest
    (fun request : QuantumMaxCutEnergy.Input × List Bool => b request.1) hb'
  obtain ⟨Pp⟩ := QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime
    QuantumMaxCutEnergy.encodeRequest
    (fun request : QuantumMaxCutEnergy.Input × List Bool => P.run request.1 request.2) hP'
  have Pv : OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeRequest
      OAI.MetricKMedian.Binary.Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (b request.1 : ℚ)) :=
    Pb.recode id (fun _ => rfl) (fun _ => rfl)
  have PA : OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeRequest
      OAI.MetricKMedian.Binary.Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (P.run request.1 request.2 : ℚ)) :=
    Pp.recode id (fun _ => rfl) (fun _ => rfl)
  exact QMCNumericRuntime.EstimatorComposition.withFloor_polynomialTime P b Pv PA
