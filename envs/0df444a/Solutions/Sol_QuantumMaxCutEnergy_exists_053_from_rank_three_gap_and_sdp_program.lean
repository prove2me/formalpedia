-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_053_from_rank_three_gap_and_sdp_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:57:13.986516+00:00
-- url     : https://prove2.me/submissions/6ebe276f-932a-48a7-a937-47d630cde3a8

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_QuantumMaxCutEnergy_agm_incident_floorValue_bounds
import Theorems.Thm_QuantumMaxCutEnergy_agm_product_value_scaling
import Theorems.Thm_QuantumMaxCutEnergy_agm_numeric_candidate_combination
import Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_structural_domination
import Mathlib

noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary

namespace QuantumMaxCutEnergy

/-- The weighted adjacency matrix of the campaign: `wMatrix G i j = w i j` off the diagonal. -/
def wMatrixAux (G : QuantumMaxCutEnergy.Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

end QuantumMaxCutEnergy

theorem solution
    (hgap : ∀ (G : QuantumMaxCutEnergy.Input) (S : ℝ),
      ModernConvex.Relaxations.IsMaxcutSDPValue
        (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S →
      (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G)
    (hprog : ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun request : QuantumMaxCutEnergy.Input × List Bool => (L request.1 : ℚ))) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧ S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.53 : ℝ) := by
  classical
  obtain ⟨L, ⟨PL⟩, hL⟩ := hprog
  -- the deterministic product candidate `0.954 * L`
  let v : Input → ℚ≥0 := fun G => ⟨(477 / 500 : ℚ) * (L G : ℚ), by
    have := (L G).2; positivity⟩
  have hvq : ∀ G, (v G : ℚ) = (477 / 500 : ℚ) * (L G : ℚ) := fun G => rfl
  have hvcast : ∀ G, (v G : ℝ) = (0.954 : ℝ) * (L G : ℝ) := by
    intro G
    have h1 : ((477 / 500 : ℚ) * (L G : ℚ) : ℚ) = (v G : ℚ) := (hvq G).symm
    have h2 : ((v G : ℚ) : ℝ) = (v G : ℝ) := by push_cast; ring
    rw [← h2, ← h1]
    push_cast
    norm_num
  -- its finite Boolean program: multiply the SDP program's output by `477/500`
  have Pc : PolyProgram encodeRequest Ratio.encode
      (fun _ : Input × List Bool => (477 / 500 : ℚ)) :=
    PolyProgram.constant _ _ _
  have Pv : PolyProgram encodeRequest Ratio.encode
      (fun request : Input × List Bool => (v request.1 : ℚ)) :=
    ((Pc.fanout PL).comp PolyProgram.ratMul).congr _ (fun request => rfl)
  -- the deterministic algorithm with output `v`
  let Av : Algorithm := { randomFactor := 0, randomDegree := 0, run := fun G _ => v G }
  -- the running maximum with the concrete matching/forest estimator
  let A : Algorithm := QMCNumericRuntime.EstimatorComposition.withFloor Av
    QMCNumericRuntime.IncidentRuntime.floorValue
  have hpoly : PolynomialTime A :=
    QMCNumericRuntime.EstimatorComposition.withFloor_polynomialTime Av _
      QMCNumericRuntime.IncidentRuntime.floorRationalProgram Pv
  refine ⟨A, hpoly, ?_⟩
  have hfloor_le : ∀ G, (QMCNumericRuntime.IncidentRuntime.floorValue G : ℝ) ≤ optimum G :=
    fun G => (QuantumMaxCutEnergy.agm_incident_floorValue_bounds G).1
  have hv_le : ∀ G, (v G : ℝ) ≤ optimum G := by
    intro G
    obtain ⟨S, hS, hLS, herror⟩ := hL G
    have hsc := QuantumMaxCutEnergy.agm_product_value_scaling (optimum G)
      (∑ e, (G.weights e : ℝ)) S (L G)
      (QuantumMaxCutEnergy.agm_sdp_structural_domination G S hS) (hgap G S hS)
      (by positivity) hLS herror
    rw [hvcast G]
    exact hsc.2.1
  intro G
  constructor
  · intro r
    exact QMCNumericRuntime.EstimatorComposition.withFloor_sound Av _
      hfloor_le (fun G _ => hv_le G) G r
  · obtain ⟨-, m, f, hm0, hmf, hfW, hupper, hf, hmm⟩ :=
      QuantumMaxCutEnergy.agm_incident_floorValue_bounds G
    obtain ⟨S, hS, hLS, herror⟩ := hL G
    have hsc := QuantumMaxCutEnergy.agm_product_value_scaling (optimum G)
      (∑ e, (G.weights e : ℝ)) S (L G)
      (QuantumMaxCutEnergy.agm_sdp_structural_domination G S hS) (hgap G S hS)
      (by positivity) hLS herror
    have hE1 : (QMCNumericRuntime.IncidentRuntime.floorValue G : ℝ) ≤
        QMCNumericRuntime.EstimatorComposition.expectedValue A G :=
      QMCNumericRuntime.EstimatorComposition.expectedValue_withFloor_ge_floor Av _ G
    have hAv : QMCNumericRuntime.EstimatorComposition.expectedValue Av G = (v G : ℝ) := by
      simp [QMCNumericRuntime.EstimatorComposition.expectedValue, Av]
    have hE2 : (v G : ℝ) ≤ QMCNumericRuntime.EstimatorComposition.expectedValue A G := by
      rw [← hAv]
      exact QMCNumericRuntime.EstimatorComposition.expectedValue_withFloor_ge_candidate Av _ G
    have hforest : f ≤ QMCNumericRuntime.EstimatorComposition.expectedValue A G := le_trans hf hE1
    have hmatching : ((∑ e, (G.weights e : ℝ)) + 3 * m) / 2 ≤
        QMCNumericRuntime.EstimatorComposition.expectedValue A G := le_trans hmm hE1
    have hproduct : (0.953 : ℝ) *
        (optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
        QMCNumericRuntime.EstimatorComposition.expectedValue A G := by
      refine le_trans ?_ hE2
      rw [hvcast G]
      exact hsc.2.2
    have hcomb := QuantumMaxCutEnergy.agm_numeric_candidate_combination (0.953 : ℝ)
      (∑ e, (G.weights e : ℝ)) m f (optimum G)
      (QMCNumericRuntime.EstimatorComposition.expectedValue A G) (by norm_num)
      hupper hforest hmatching hproduct
    have hO0 : (0 : ℝ) ≤ optimum G := le_trans hm0 (le_trans hmf (le_trans hf (hfloor_le G)))
    · -- expected values are exactly the model's finite average
      show (0.53 : ℝ) * optimum G ≤
        (∑ r : Fin (randomBits A G) → Bool, (A.run G (List.ofFn r) : ℝ)) /
          (Fintype.card (Fin (randomBits A G) → Bool) : ℝ)
      have hstep1 : (0.53 : ℝ) * optimum G ≤
          (11 * 0.953 / (15 + 5 * 0.953)) * optimum G := by
        have hc : (0.53 : ℝ) ≤ 11 * 0.953 / (15 + 5 * 0.953) := by norm_num
        exact mul_le_mul_of_nonneg_right hc hO0
      have hstep2 : (11 * 0.953 / (15 + 5 * 0.953)) * optimum G ≤
          QMCNumericRuntime.EstimatorComposition.expectedValue A G := by
        have hpos : (0 : ℝ) < 15 + 5 * 0.953 := by norm_num
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        linarith [hcomb]
      exact le_trans hstep1 hstep2

