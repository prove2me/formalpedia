-- Prove2me | solution 3 for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:24:33.070788+00:00
-- url     : https://prove2.me/submissions/8802c544-03ee-4341-900a-57535852b1b1

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
import Definitions.Def_QMCSub_Final2
open scoped BigOperators

theorem solution :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCSub.sdp_lower_value_tm2
