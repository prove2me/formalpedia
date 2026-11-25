-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:54.621679+00:00
-- url     : https://prove2.me/submissions/ab2161a6-fd34-4e69-ad2e-5b052873ce94

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isPsh_mono_158b3583c42f
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution (D : ℕ) :
    IsPsh (ball (0 : Fin D → ℂ) 2) (fun z => ∑ j, ‖z j‖ ^ 2) :=
  isPsh_mono (ReciprocityTheory.AnForm.A.isPshInhabit_thm D).1 (Set.subset_univ _)
end GroundTheory.Heights₂.Heights.Regular
