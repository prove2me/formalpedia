-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_cut_bound_11483c3c9e2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:53.819799+00:00
-- url     : https://prove2.me/submissions/18823a31-c1f5-44cd-a099-df3e044f414d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_cutoffDeriv_contDiff_b30604209685
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_cutoffSecondDeriv_continuous_0910450e5b6f

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
theorem _root_.solution : ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc (0 : ℝ) (9 / 4), -M ≤ s * cutoffSecondDeriv s + cutoffDeriv s := by
  obtain ⟨m, hm⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 9 / 4)).bddBelow_image
    (f := fun s => s * cutoffSecondDeriv s + cutoffDeriv s)
    ((continuous_id.mul cutoffSecondDeriv_continuous).add cutoffDeriv_contDiff.continuous).continuousOn
  refine ⟨max 0 (-m), le_max_left _ _, fun s hs => ?_⟩
  have h1 : m ≤ s * cutoffSecondDeriv s + cutoffDeriv s := hm ⟨s, hs, rfl⟩
  have h2 : -m ≤ max 0 (-m) := le_max_right _ _
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
