-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:37:34.861336+00:00
-- url     : https://prove2.me/submissions/45525ee3-744f-4f8c-8cdd-92e5382bdd72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_exists_polyProgram_of_tm2InPolyTime
import Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_lower_value_tm2
import Mathlib
open scoped BigOperators

theorem solution :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun request : QuantumMaxCutEnergy.Input × List Bool => (L request.1 : ℚ))) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  obtain ⟨L, ⟨hTM⟩, hnum⟩ := QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2
  refine ⟨L, ?_, hnum⟩
  have hP := QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime
    (α := QuantumMaxCutEnergy.Input × List Bool)
    (ea := QuantumMaxCutEnergy.encodeRequest)
    (f := fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1) hTM
  obtain ⟨P⟩ := hP
  exact ⟨⟨P.machine, P.time, fun a => P.outputs a⟩⟩
