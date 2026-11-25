-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_levi_fin_zero_b2d5a56817d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:33.934315+00:00
-- url     : https://prove2.me/submissions/2e2144a1-0a9d-4f41-b998-12cf3274604e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements

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
theorem _root_.solution (φ : (Fin 0 → ℂ) → ℝ) (z w : Fin 0 → ℂ) : levi φ z w = 0 := by
  rw [Subsingleton.elim w 0]
  simp only [levi, smul_zero, map_zero, _root_.zero_apply]
  norm_num
end GroundTheory.Heights₂.Heights.Regular
