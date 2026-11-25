-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ineq_self_0ba56674a6fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:56.612437+00:00
-- url     : https://prove2.me/submissions/07f219c6-7629-4985-91b3-85c84ca15fc6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood

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
open ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution (M t H : ℝ) (hM : 0 ≤ M) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 4) (h : -M ≤ H) :
    -(2 * M * (13 / 4) ^ 2) * (2 * (1 + t) ^ 2)⁻¹ ≤ H := by
  have hp : 0 < (1 + t) ^ 2 := by positivity
  have h1 : (1 + t) ^ 2 ≤ (13 / 4) ^ 2 := by nlinarith
  have h2 : -(2 * M * (13 / 4) ^ 2) * (2 * (1 + t) ^ 2)⁻¹ = -(M * (13 / 4) ^ 2 / (1 + t) ^ 2) := by
    field_simp
  have h3 : M ≤ M * (13 / 4) ^ 2 / (1 + t) ^ 2 := by
    rw [le_div_iff₀ hp]; nlinarith
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
