-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.fderiv_bound_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:39.608965+00:00
-- url     : https://prove2.me/submissions/a0f26c36-877a-465f-8ab8-642ac95787eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Theorems.Thm_Bl_general_b_fact_alt_form_goal1
import Theorems.Thm_Bl_general_b_fact_bis_form_goal1
import Theorems.Thm_Bl_general_b_fact_version_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open Metric
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
    {R M : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball y (2 * R)))
    (hM : ∀ v ∈ ball y (2 * R), ‖g v‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / R := by
  first | exact Bl.general_b_fact_version.goal1 .. | (apply Bl.general_b_fact_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_version.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
