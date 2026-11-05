-- Prove2me | solution 2 for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:13.703402+00:00
-- url     : https://prove2.me/submissions/57165c4d-4b5f-4184-b39f-82759073b4ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_certificate_program
import Theorems.Thm_ModernConvex_Relaxations_maxcutRelaxationObjective_le_sdpValue
import Theorems.Thm_ModernConvex_Relaxations_sdpValue_le_dual

open scoped BigOperators
open Matrix

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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  obtain ⟨L, X, lam, hmach, hcert⟩ := QuantumMaxCutEnergy.agm_sdp_certificate_program
  refine ⟨L, hmach, fun G => ?_⟩
  obtain ⟨S, hS, hX, hdual, hLle, hgap⟩ := hcert G
  have h1 : ModernConvex.Relaxations.maxcutRelaxationObjective
      (QuantumMaxCutEnergy.weightMatrix G) (X G) ≤ S :=
    ModernConvex.Relaxations.maxcutRelaxationObjective_le_sdpValue hX hS
  have h2 : S ≤ (1 / 4) * ((∑ i, ∑ j, QuantumMaxCutEnergy.weightMatrix G i j)
      + ∑ i, lam G i) :=
    ModernConvex.Relaxations.sdpValue_le_dual hS (lam G) hdual
  exact ⟨S, hS, by linarith, by linarith⟩
