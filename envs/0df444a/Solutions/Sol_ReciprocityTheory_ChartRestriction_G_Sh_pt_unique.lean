-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:00.679157+00:00
-- url     : https://prove2.me/submissions/82f9c8a5-ee31-437e-ad28-c70bba47cdf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptAgree_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
variable (T : (ι → MvPowerSeries τ R) → (ι → MvPowerSeries τ R))
  (P : (ι → MvPowerSeries τ R) → Prop)
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution
    (hT : ∀ k x y, P x → P y → PTAgree k x y → PTAgree (k + 1) (T x) (T y))
    {x y : ι → MvPowerSeries τ R} (hx : P x) (hy : P y) (hTx : T x = x) (hTy : T y = y) :
    x = y := by
  refine ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.eq fun k => ?_
  induction k with
  | zero => exact ptAgree_zero _ _
  | succ k ih =>
    have h := hT k x y hx hy ih
    rwa [hTx, hTy] at h
end ReciprocityTheory.ChartRestriction.G.Sh
