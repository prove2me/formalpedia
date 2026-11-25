-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_mollifier_bounded_inhabited_12874e05e8e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:56.932228+00:00
-- url     : https://prove2.me/submissions/ff0ef067-4cf4-4f53-8c04-3b130a527a1d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollifierInhabit_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (polyMax Mollifier molli regMax coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart maMeasure)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution (D : ℕ) : ∃ (ρ : Mollifier D) (B : ℝ), ∀ w, ρ.toFun w ≤ B := by
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  have hc : HasCompactSupport ρ.toFun := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 1) fun x hx => ?_
    by_contra h
    exact hx (ball_subset_closedBall (ρ.support_subset (Function.mem_support.2 h)))
  obtain ⟨B, hB⟩ := ρ.contDiff.continuous.bddAbove_range_of_hasCompactSupport hc
  exact ⟨ρ, B, fun w => hB ⟨w, rfl⟩⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
