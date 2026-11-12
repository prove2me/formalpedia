-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.observation_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:31:10.818035+00:00
-- url     : https://prove2.me/submissions/5fb3989b-0149-4ef5-9401-7b6c2387219d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_observation_original
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26NativeGeometricExecution
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    observation S n J hr lambda K T =
      Resampling.VariableRelabeling.jointObservation (U S n J r) (B S n J r lambda K)
        (decodedTable S n T) := by
  have h := observation_original S n J hr lambda K (decodedTable S n T)
  rw [encoded_decoded] at h
  exact h
end QEC.Coding.BDL26NativeGeometricExecution
