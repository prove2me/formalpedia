-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_polyMaxOscillation_hyp_24d63f9fc5e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:00.653291+00:00
-- url     : https://prove2.me/submissions/9f15478f-2298-4192-8b78-08268dc60772

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220

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
theorem _root_.solution (D : ℕ) :
    IsOpen (ball (0 : Fin D → ℂ) 2) ∧ IsPsh (ball (0 : Fin D → ℂ) 2) (fun z => ∑ j, ‖z j‖ ^ 2) ∧
      closedBall (0 : Fin D → ℂ) 1 ⊆ ball 0 2 ∧ (0 : ℝ) < 1 / 4 ∧ (1 : ℝ) ≤ 1 ∧
      (1 : ℝ) * (1 / 4) < 1 :=
  ⟨isOpen_ball, isPsh_normSq_ball D, closedBall_subset_ball (by norm_num), by norm_num, le_rfl,
    by norm_num⟩
end GroundTheory.Heights₂.Heights.Regular
