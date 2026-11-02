-- Prove2me | solution 1 for QuantumMaxCutEnergy.ratio_frame_recode
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:21:45.564933+00:00
-- url     : https://prove2.me/submissions/1d111348-7844-4145-9134-2534db3aa0ca

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
open scoped BigOperators

theorem solution :
    Nonempty (OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeValue
      (fun q : ℚ≥0 => OAI.MetricKMedian.Binary.Ratio.encode (q : ℚ)) id) := by
  have hfst : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun xs : List Bool => (QMCNumericRuntime.readWeight xs).1) :=
    OAI.MetricKMedian.Binary.Automatic.Poly.comp
      (OAI.MetricKMedian.Binary.Automatic.Poly.fst (α := ℚ) (β := List Bool))
      QMCNumericRuntime.readWeight_poly
  have P : OAI.MetricKMedian.Binary.PolyProgram id OAI.MetricKMedian.Binary.Ratio.encode
      (fun xs : List Bool => (QMCNumericRuntime.readWeight xs).1) :=
    (OAI.MetricKMedian.Binary.BooleanLists.packProgram.comp hfst.program).congr _ (fun _ => rfl)
  refine ⟨P.recode QuantumMaxCutEnergy.encodeValue (fun _ => rfl) (fun q => ?_)⟩
  have h := QMCNumericRuntime.readWeight_append q []
  rw [List.append_nil] at h
  simp only [QuantumMaxCutEnergy.encodeValue, h, id]
