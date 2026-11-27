-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_mollifiedLowerBound_hyp_9e4921481e91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:50.394633+00:00
-- url     : https://prove2.me/submissions/dbe9de95-52e2-4c69-8218-58db44889363

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution (D : ℕ) : ∃ (ρ : Mollifier D) (b : ℝ),
    IsOpen (ball (0 : Fin D → ℂ) 2) ∧ IsPsh (ball (0 : Fin D → ℂ) 2) (fun z => ∑ j, ‖z j‖ ^ 2) ∧
      (0 : ℝ) < 1 / 2 ∧ closedBall (0 : Fin D → ℂ) (2 * (1 / 2)) ⊆ ball 0 2 ∧
      ∀ w, ρ.toFun w ≤ b := by
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  exact ⟨ρ, b, isOpen_ball, isPsh_normSq_ball D, by norm_num,
    closedBall_subset_ball (by norm_num), hb⟩
end GroundTheory.Heights₂.Heights.Regular
