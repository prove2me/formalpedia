-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_levi_cut_other_dc1cd7a6f0e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:59.621784+00:00
-- url     : https://prove2.me/submissions/2649367b-79a8-44e5-b684-8fb1d420f3cb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hasDerivAt_cutG_611e9e10a524
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hasDerivAt_cutoffDeriv_de17c72e1c35
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_leviForm_radial


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
theorem _root_.solution (y w : Fin 1 → ℂ) (hy : y 0 ≠ 0) :
    levi (fun y : Fin 1 → ℂ => cutG ((‖y 0‖ ^ 2)⁻¹)) y w =
      ((‖y 0‖ ^ 2)⁻¹) ^ 2 * ((‖y 0‖ ^ 2)⁻¹ * cutoffSecondDeriv ((‖y 0‖ ^ 2)⁻¹) + cutoffDeriv ((‖y 0‖ ^ 2)⁻¹)) *
        ‖w 0‖ ^ 2 := by
  have htp : 0 < ‖y 0‖ ^ 2 := by have := norm_pos_iff.2 hy; positivity
  have hG : ∀ s : ℝ, s ≠ 0 → HasDerivAt (fun s => cutG s⁻¹) (cutoffDeriv s⁻¹ * -(s ^ 2)⁻¹) s :=
    fun s hs => (hasDerivAt_cutG s⁻¹).comp s (hasDerivAt_inv hs)
  have h1 : HasDerivAt (fun s : ℝ => cutoffDeriv s⁻¹)
      (cutoffSecondDeriv (‖y 0‖ ^ 2)⁻¹ * -((‖y 0‖ ^ 2) ^ 2)⁻¹) (‖y 0‖ ^ 2) :=
    (hasDerivAt_cutoffDeriv _).comp _ (hasDerivAt_inv htp.ne')
  have h2 : HasDerivAt (fun s : ℝ => -(s ^ 2)⁻¹)
      (2 * ‖y 0‖ ^ 2 / ((‖y 0‖ ^ 2) ^ 2) ^ 2) (‖y 0‖ ^ 2) := by
    have := ((hasDerivAt_pow 2 (‖y 0‖ ^ 2)).inv (pow_ne_zero 2 htp.ne')).neg
    exact this.congr_deriv (by norm_num [neg_div])
  rw [projLine_leviForm_radial (G := fun s => cutG s⁻¹) (G' := fun s => cutoffDeriv s⁻¹ * -(s ^ 2)⁻¹)
    (Filter.Eventually.of_forall fun _ => rfl) ?_ (h1.mul h2) w]
  · congr 1
    field_simp
    ring
  · filter_upwards [eventually_ne_nhds htp.ne'] with s hs
    exact hG s hs
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
