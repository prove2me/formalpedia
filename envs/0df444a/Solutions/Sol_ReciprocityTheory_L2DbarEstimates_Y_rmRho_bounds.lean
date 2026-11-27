-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmRho_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:53.235368+00:00
-- url     : https://prove2.me/submissions/a02fe796-006d-443b-b288-86c077011ab5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_hasDerivAt
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_even
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_of_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_lip

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
theorem _root_.solution (t : ℝ) : |t| ≤ rmRho t ∧ rmRho t ≤ |t| + 1 := by
  have h12 : rmRho (1 / 2) = 1 / 2 := by
    unfold rmRho
    ring
  have hanti : Antitone (fun x => rmRho x - x) := by
    have hd : ∀ x, HasDerivAt (fun x => rmRho x - x) (rmRho' x - 1) x :=
      fun x => (rmRho_hasDerivAt x).sub (hasDerivAt_id x)
    refine antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]
    have := (abs_le.mp (abs_rmRho'_le x)).2
    linarith
  have hge : ∀ s : ℝ, s ≤ rmRho s := by
    intro s
    rcases le_or_gt s (1 / 2) with hs | hs
    · have := hanti hs
      simp only at this
      linarith
    · rw [rmRho_of_le s hs.le]
  constructor
  · rw [abs_le]
    constructor
    · have := hge (-t)
      rw [rmRho_even] at this
      linarith
    · exact hge t
  · have hl := rmRho_lip t (1 / 2)
    have hA : |t - 1 / 2| ≤ |t| + 1 / 2 := abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := le_abs_self (rmRho t - rmRho (1 / 2))
    linarith
end ReciprocityTheory.L2DbarEstimates.Y
