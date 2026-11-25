-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_v_intCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:11.126865+00:00
-- url     : https://prove2.me/submissions/6fe45938-69ee-4d5d-9570-b3f3373bb73e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_v_natCast_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (n : ℤ) : (0 : WithTop ℝ) ≤ v (n : C) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_coe, Int.cast_natCast]; exact pt_v_natCast_nonneg m
  | negSucc m => rw [Int.cast_negSucc, v.map_neg]; exact pt_v_natCast_nonneg (m + 1)
end ReciprocityTheory.ChartRestriction.G.Sh
