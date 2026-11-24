-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:31.407586+00:00
-- url     : https://prove2.me/submissions/94c68110-5f43-4521-bb0b-9c3a6cd8046d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {D : ℕ} (ρ : Mollifier D) : ∃ b : ℝ, ∀ w, ρ.toFun w ≤ b := by
  have hc : Continuous ρ.toFun := ρ.contDiff.continuous
  have hs : HasCompactSupport ρ.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 1) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall (ρ.support_subset (Function.mem_support.mpr h)))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, fun w => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC w)⟩
end GroundTheory.Heights₂.Heights.Regular
