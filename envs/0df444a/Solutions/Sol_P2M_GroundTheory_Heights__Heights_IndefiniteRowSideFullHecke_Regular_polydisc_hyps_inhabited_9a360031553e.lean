-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_polydisc_hyps_inhabited_9a360031553e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:01:36.635844+00:00
-- url     : https://prove2.me/submissions/c88af751-176b-44b3-a412-3baeeac18c7f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_ReciprocityTheory_AnForm_A_isPshInhabit_thm


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
theorem _root_.solution (D : ℕ) :
    IsOpen (Set.univ : Set (Fin D → ℂ)) ∧
      ReciprocityTheory.AnForm.A.IsPsh Set.univ (fun z : Fin D → ℂ => ∑ j, ‖z j‖ ^ 2) ∧
      closedBall (0 : Fin D → ℂ) (2 * 1) ⊆ Set.univ ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) * 1 < 2 :=
  ⟨isOpen_univ, (ReciprocityTheory.AnForm.A.isPshInhabit_thm D).1, Set.subset_univ _, le_rfl, one_pos,
    by norm_num⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
