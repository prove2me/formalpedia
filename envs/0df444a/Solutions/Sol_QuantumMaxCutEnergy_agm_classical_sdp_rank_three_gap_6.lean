-- Prove2me | solution 6 for QuantumMaxCutEnergy.agm_classical_sdp_rank_three_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:21:03.101375+00:00
-- url     : https://prove2.me/submissions/84da9eab-4593-4277-a82e-257ab5a564ea

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_sdp_gap_iff_pointwise
import Theorems.Thm_QuantumMaxCutEnergy_rank_three_rounding_pointwise
import Mathlib
open scoped BigOperators

theorem solution (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G := by
  refine (QuantumMaxCutEnergy.sdp_gap_iff_pointwise
    (Matrix.of fun i j : Fin G.n =>
      if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)
    S 0.954 (QuantumMaxCutEnergy.optimum G) (by norm_num) hS).mpr ?_
  intro X hX
  exact QuantumMaxCutEnergy.rank_three_rounding_pointwise G X hX
