-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ineq_other_5477bc668218
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:58.502659+00:00
-- url     : https://prove2.me/submissions/0bb9648b-40b5-4cbc-a664-b2d72471db05

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
theorem _root_.solution (M t H : ℝ) (hM : 0 ≤ M) (ht0 : 0 < t) (hs : t⁻¹ ≤ 9 / 4) (h : -M ≤ H) :
    -(2 * M * (13 / 4) ^ 2) * (2 * (1 + t) ^ 2)⁻¹ ≤ (t⁻¹) ^ 2 * H := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ t = s⁻¹ := ⟨t⁻¹, inv_pos.2 ht0, (inv_inv t).symm⟩
  rw [inv_inv] at hs ⊢
  have hp : 0 < (1 + s) ^ 2 := by positivity
  have h1 : (1 + s) ^ 2 ≤ (13 / 4) ^ 2 := by nlinarith
  have h2 : -(2 * M * (13 / 4) ^ 2) * (2 * (1 + s⁻¹) ^ 2)⁻¹ =
      -(M * (13 / 4) ^ 2 * s ^ 2 / (1 + s) ^ 2) := by
    field_simp
    ring
  have h3 : M * s ^ 2 ≤ M * (13 / 4) ^ 2 * s ^ 2 / (1 + s) ^ 2 := by
    rw [le_div_iff₀ hp]
    nlinarith [mul_nonneg (mul_nonneg hM (sq_nonneg s)) (sub_nonneg.2 h1)]
  have h4 : -(M * s ^ 2) ≤ s ^ 2 * H := by
    nlinarith [mul_nonneg (sq_nonneg s) (by linarith : 0 ≤ H + M)]
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
