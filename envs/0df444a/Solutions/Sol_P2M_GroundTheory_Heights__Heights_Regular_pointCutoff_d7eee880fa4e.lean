-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_pointCutoff_d7eee880fa4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:15.681426+00:00
-- url     : https://prove2.me/submissions/c3ad9084-87fe-4fba-8ecd-69a1a9ff5962

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_levi_fin_zero_b2d5a56817d4

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
theorem _root_.solution : pointCharts.IsCutoffFamily (fun _ _ => 0) 1 where
  smooth _ _ := contDiffOn_const
  bounds _ _ _ := ⟨by norm_num, le_rfl⟩
  eq_zero _ _ _ := rfl
  eq_neg_one _ := ⟨Set.univ, isClosed_univ, subset_rfl, fun x hx => absurd (Set.mem_univ x) hx.2⟩
  levi_ge _ _ _ _ w := by rw [levi_fin_zero]; simp [Subsingleton.elim w 0]
end GroundTheory.Heights₂.Heights.Regular
