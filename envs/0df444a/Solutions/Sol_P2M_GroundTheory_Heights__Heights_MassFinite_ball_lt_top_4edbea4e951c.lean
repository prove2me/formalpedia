-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFinite_ball_lt_top_4edbea4e951c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:35.00509+00:00
-- url     : https://prove2.me/submissions/d1e45190-f372-433a-833c-f802bbf5ca20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite
namespace GroundTheory.Heights₂.Heights.MassFinite
theorem _root_.solution {ι : Type*} [Fintype ι] (R : ℝ) :
    μH[((2 * Fintype.card ι : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R) < ⊤ := by
  have hfr : Module.finrank ℝ (ι × Fin 2 → ℝ) = Module.finrank ℝ (EuclideanSpace ℂ ι) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]
  let e := (LinearEquiv.ofFinrankEq _ _ hfr).toContinuousLinearEquiv
  have hcard : ((2 * Fintype.card ι : ℕ) : ℝ) = ((Fintype.card (ι × Fin 2) : ℕ) : ℝ) := by
    simp [mul_comm]
  have hsub : Metric.ball (0 : EuclideanSpace ℂ ι) R ⊆ e '' (e.symm '' Metric.ball 0 R) := by
    rw [Set.image_image]
    simp
  have hb : Bornology.IsBounded (e.symm '' Metric.ball (0 : EuclideanSpace ℂ ι) R) :=
    e.symm.lipschitz.isBounded_image Metric.isBounded_ball
  rw [hcard]
  calc μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R)
      ≤ μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (e '' (e.symm '' Metric.ball 0 R)) := measure_mono hsub
    _ ≤ _ := e.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
      rw [hausdorffMeasure_pi_real]
      exact hb.measure_lt_top
end GroundTheory.Heights₂.Heights.MassFinite
