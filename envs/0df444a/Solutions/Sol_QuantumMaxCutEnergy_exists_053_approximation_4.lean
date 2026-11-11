-- Prove2me | solution 4 for QuantumMaxCutEnergy.exists_053_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:54:25.407196+00:00
-- url     : https://prove2.me/submissions/09afe97d-1656-439b-a130-8f08d11b4cd8

/-
Main theorem of the mission, reduced to ONE open child.

Instead of `max(b G, P.run G r)` at the `Algorithm` level (which needs the TM2-closure
statement `polynomialTime_max_with_deterministic_estimator`, not provable from the
available API), this proof stays one level down: both candidates are `PolyProgram`s,
the pointwise maximum of two rational programs is `rationalMaximumProgram`, and
`QMCNumericRuntime.EstimatorComposition.withFloor_polynomialTime` turns the pair into a
genuine `Algorithm` with a `PolynomialTime` certificate.  Hence the main theorem follows
from leaf 8462331b (`agm_deterministic_product_value_program`) alone, plus the proved
`agm_incident_floorValue_bounds` (concrete matching/forest candidate) and definitions-file
glue.  In particular leaves 1, 3, 4, 5 are not on the critical path.
-/
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_QuantumMaxCutEnergy_agm_incident_floorValue_bounds
import Theorems.Thm_QuantumMaxCutEnergy_agm_deterministic_product_value_program
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

namespace QMC053Sharp

/-- Uniform average of a constant over a finite Boolean tape. -/
lemma const_average (k : ℕ) (c : ℝ) :
    (∑ _r : Fin k → Bool, c) / (Fintype.card (Fin k → Bool) : ℝ) = c := by
  have hc : (Fintype.card (Fin k → Bool) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Algebraic core of `agm_numeric_candidate_combination` (self-contained). -/
lemma numeric_combination (β W m f O E : ℝ) (hβ : 0 ≤ β)
    (hupper : O ≤ W + (m + f) / 2) (hforest : f ≤ E)
    (hmatching : (W + 3 * m) / 2 ≤ E) (hproduct : β * (O + W) / 3 ≤ E) :
    11 * β * O ≤ (15 + 5 * β) * E := by
  rcases eq_or_lt_of_le hβ with hβ0 | hβpos
  · have hE : 0 ≤ E := by rw [← hβ0] at hproduct; linarith
    rw [← hβ0]; nlinarith
  · have h1 : 6 * O ≤ 5 * W + 5 * E := by
      have hm : 3 * m ≤ 2 * E - W := by linarith
      linarith
    have h2 : β * O + β * W ≤ 3 * E := by nlinarith
    have h3 : β * W ≤ 3 * E - β * O := by linarith
    have h4 : 6 * β * O ≤ 5 * (β * W) + 5 * (β * E) := by
      have h := mul_le_mul_of_nonneg_left h1 hβpos.le
      nlinarith
    nlinarith

/-- The tape-independent algorithm attached to a deterministic candidate. -/
def detAlg (p : QuantumMaxCutEnergy.Input → ℚ≥0) : QuantumMaxCutEnergy.Algorithm where
  randomFactor := 0
  randomDegree := 0
  run := fun G _ => p G

@[simp] lemma detAlg_randomBits (p : QuantumMaxCutEnergy.Input → ℚ≥0)
    (G : QuantumMaxCutEnergy.Input) :
    QuantumMaxCutEnergy.randomBits (detAlg p) G = 0 := by
  simp [detAlg, QuantumMaxCutEnergy.randomBits]

/-- A tape-independent algorithm has expectation equal to its single value. -/
lemma expectedValue_det (p : QuantumMaxCutEnergy.Input → ℚ≥0)
    (G : QuantumMaxCutEnergy.Input) :
    QMCNumericRuntime.EstimatorComposition.expectedValue (detAlg p) G = (p G : ℝ) := by
  have hsum : (∑ r : Fin (QuantumMaxCutEnergy.randomBits (detAlg p) G) → Bool,
      ((detAlg p).run G (List.ofFn r) : ℝ)) = (p G : ℝ) := by
    rw [detAlg_randomBits]
    simp [detAlg]
  simp only [QMCNumericRuntime.EstimatorComposition.expectedValue]
  rw [hsum, detAlg_randomBits]
  have hcard : (Fintype.card (Fin 0 → Bool) : ℝ) = 1 := by norm_num
  rw [hcard, div_one]

end QMC053Sharp

open scoped BigOperators

theorem solution :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.53 : ℝ) := by
  obtain ⟨p, ⟨Pp⟩, hp⟩ := QuantumMaxCutEnergy.agm_deterministic_product_value_program
  -- the randomized product candidate, made deterministic on the empty tape
  let A : QuantumMaxCutEnergy.Algorithm := QMC053Sharp.detAlg p
  -- the concrete matching/forest candidate from the definition file
  let v : QuantumMaxCutEnergy.Input → ℚ≥0 := QMCNumericRuntime.IncidentRuntime.floorValue
  let PA : OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeRequest
      OAI.MetricKMedian.Binary.Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (A.run request.1 request.2 : ℚ)) := Pp
  let Pv : OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeRequest
      OAI.MetricKMedian.Binary.Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (v request.1 : ℚ)) :=
    QMCNumericRuntime.IncidentRuntime.floorRationalProgram
  have hvle : ∀ G, (v G : ℝ) ≤ QuantumMaxCutEnergy.optimum G :=
    fun G => (QuantumMaxCutEnergy.agm_incident_floorValue_bounds G).1
  have hAle : ∀ G (r : Fin (QuantumMaxCutEnergy.randomBits A G) → Bool),
      (A.run G (List.ofFn r) : ℝ) ≤ QuantumMaxCutEnergy.optimum G :=
    fun G _ => (hp G).1
  refine ⟨QMCNumericRuntime.EstimatorComposition.withFloor A v,
    QMCNumericRuntime.EstimatorComposition.withFloor_polynomialTime A v Pv PA, ?_⟩
  intro G
  refine ⟨QMCNumericRuntime.EstimatorComposition.withFloor_sound A v hvle hAle G, ?_⟩
  obtain ⟨-, m, f, -, -, -, hupper, hfb, hmatch⟩ :=
    QuantumMaxCutEnergy.agm_incident_floorValue_bounds G
  have hEA : ∀ G, (p G : ℝ) ≤ QMCNumericRuntime.EstimatorComposition.expectedValue A G := by
    intro G
    rw [QMC053Sharp.expectedValue_det]
  have hmax := QMCNumericRuntime.EstimatorComposition.withFloor_expected_lower
    (A := A) (v := v) (L := fun G => (p G : ℝ)) hEA G
  obtain ⟨hvm, hpm⟩ := max_le_iff.mp hmax
  have hE0 : (0 : ℝ) ≤ QMCNumericRuntime.EstimatorComposition.expectedValue
      (QMCNumericRuntime.EstimatorComposition.withFloor A v) G :=
    le_trans (by positivity : (0 : ℝ) ≤ (v G : ℝ)) hvm
  have hcomb := QMC053Sharp.numeric_combination (0.953 : ℝ) (∑ e, (G.weights e : ℝ)) m f
    (QuantumMaxCutEnergy.optimum G)
    (QMCNumericRuntime.EstimatorComposition.expectedValue
      (QMCNumericRuntime.EstimatorComposition.withFloor A v) G)
    (by norm_num) hupper (le_trans hfb hvm) (le_trans hmatch hvm) (le_trans (hp G).2 hpm)
  change (0.53 : ℝ) * QuantumMaxCutEnergy.optimum G ≤
    QMCNumericRuntime.EstimatorComposition.expectedValue
      (QMCNumericRuntime.EstimatorComposition.withFloor A v) G
  linarith [hcomb, hE0]
