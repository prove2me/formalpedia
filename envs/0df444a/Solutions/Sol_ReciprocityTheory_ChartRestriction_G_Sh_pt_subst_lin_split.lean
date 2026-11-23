-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_subst_lin_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:10.918751+00:00
-- url     : https://prove2.me/submissions/f3e9a769-e938-4bdb-bc6b-4e40b7097df2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff

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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ τ : Type*} [Fintype σ] {x : σ → MvPowerSeries τ C}
    (hx : HasSubst x) (Φ : MvPowerSeries σ C) (m : σ → C) :
    subst x Φ = ∑ a, m a • x a + subst x (Φ - ∑ a, m a • X a) := by
  have hs : subst x (∑ a, m a • X a : MvPowerSeries σ C) = ∑ a, m a • x a := by
    rw [← MvPowerSeries.coe_substAlgHom hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hx, MvPowerSeries.subst_smul hx, MvPowerSeries.subst_X hx]
  rw [MvPowerSeries.subst_sub hx, hs]
  abel
end ReciprocityTheory.ChartRestriction.G.Sh
