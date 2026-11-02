-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:43:02.752564+00:00
-- url     : https://prove2.me/submissions/d7735346-90e9-4974-8769-1afb74108c14

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_QuantumMaxCutEnergy_tm2_to_boolean_stacks
import Theorems.Thm_QuantumMaxCutEnergy_ratio_frame_recode
open scoped BigOperators

theorem solution
    {α : Type} (ea : α → List Bool) (f : α → ℚ≥0)
    (h : Turing.TM2ComputableInPolyTime ea QuantumMaxCutEnergy.encodeValue f) :
    Nonempty (OAI.MetricKMedian.Binary.PolyProgram ea
      (fun q : ℚ≥0 => OAI.MetricKMedian.Binary.Ratio.encode (q : ℚ)) f) := by
  obtain ⟨P⟩ := QuantumMaxCutEnergy.tm2_to_boolean_stacks ea f ⟨h⟩
  obtain ⟨Q⟩ := QuantumMaxCutEnergy.ratio_frame_recode
  exact ⟨P.comp Q⟩
