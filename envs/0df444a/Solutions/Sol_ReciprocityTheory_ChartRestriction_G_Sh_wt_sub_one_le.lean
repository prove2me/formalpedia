-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.wt_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:14.721981+00:00
-- url     : https://prove2.me/submissions/43eb0600-87c8-491f-a9ad-700d895494dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TypicalCurveStructureConstants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {r : ℝ} {y : WithTop ℝ} (h : (r : WithTop ℝ) ≤ 1 + y) :
    ((r - 1 : ℝ) : WithTop ℝ) ≤ y := by
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    have h1 : ((1 : WithTop ℝ) + (a : WithTop ℝ)) = ((1 + a : ℝ) : WithTop ℝ) := by
      norm_cast
    rw [h1, WithTop.coe_le_coe] at h
    exact WithTop.coe_le_coe.mpr (by linarith)
end ReciprocityTheory.ChartRestriction.G.Sh
