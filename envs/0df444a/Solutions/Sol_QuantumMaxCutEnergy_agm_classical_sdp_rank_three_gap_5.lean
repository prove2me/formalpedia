-- Prove2me | solution 5 for QuantumMaxCutEnergy.agm_classical_sdp_rank_three_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:08:24.571684+00:00
-- url     : https://prove2.me/submissions/851c7ccb-5105-4b89-8d3b-e3ed45fae966
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QuantumMaxCutEnergy_rank_three_rounding_pointwise
import Theorems.Thm_QuantumMaxCutEnergy_sdp_gap_iff_pointwise
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib

open scoped BigOperators

theorem solution
    (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G := by
  have key := QuantumMaxCutEnergy.sdp_gap_iff_pointwise
    (Matrix.of fun i j : Fin G.n =>
      if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)
    S 0.954 (QuantumMaxCutEnergy.optimum G) (by norm_num) hS
  exact key.mpr fun X hX => QuantumMaxCutEnergy.rank_three_rounding_pointwise G X hX
