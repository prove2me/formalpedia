-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmRho_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:18.442399+00:00
-- url     : https://prove2.me/submissions/1d20f94f-c6ff-4db2-8f98-3f36307fe0dd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmPrim_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (t : ℝ) : HasDerivAt rmRho (rmRho' t) t := by
  have h1 := rmPrim_hasDerivAt t
  have h2 : HasDerivAt (fun s => rmPrim (-s)) (-rmStep (-t)) t := by
    have := (rmPrim_hasDerivAt (-t)).comp t (hasDerivAt_neg t)
    rw [mul_neg_one] at this
    exact this
  have h3 := ((h1.add h2).div_const 2).add_const (1 / 2 - rmRho0 (1 / 2))
  have h4 : rmRho' t = (rmStep t + -rmStep (-t)) / 2 := by
    unfold rmRho'
    ring
  rw [h4]
  exact h3
end ReciprocityTheory.L2DbarEstimates.Y
