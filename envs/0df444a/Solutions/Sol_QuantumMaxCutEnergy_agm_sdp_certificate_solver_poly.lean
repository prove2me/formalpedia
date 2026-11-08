-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_sdp_certificate_solver_poly
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:13:17.042856+00:00
-- url     : https://prove2.me/submissions/7c4990f7-d0cd-4bc0-b1bc-292e25ec8b8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer
import Theorems.Thm_QMCLeafB_exists_slack_engine
import Theorems.Thm_QMCLeafB_Engine_to_solver_poly

open scoped BigOperators

theorem solution : ∃ Solve : List QMCNumericRuntime.NumericEdge → List (List ℚ) × List ℚ, OAI.MetricKMedian.Binary.Automatic.Poly Solve ∧ ∀ G : QuantumMaxCutEnergy.Input, ModernConvex.Relaxations.IsUnitDiagPSD (Matrix.of fun i j : Fin G.n => ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ∧ (Matrix.diagonal (fun i : Fin G.n => (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ)) + (1 / 4 : ℝ) • (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧ (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) + ∑ i : Fin G.n, (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ) - ModernConvex.Relaxations.maxcutRelaxationObjective (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) (Matrix.of fun i j : Fin G.n => ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  obtain ⟨eng, _⟩ := QMCLeafB_exists_slack_engine
  exact QMCLeafB_Engine_to_solver_poly eng
