-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:02.002818+00:00
-- url     : https://prove2.me/submissions/937eba79-c8b5-4b34-a521-7bd6734121b9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst

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
theorem _root_.solution {σ : Type*} {c : C} (hc : c ∈ ptIntSub v) {f : MvPowerSeries σ C}
    (hf : f ∈ ptIntSer v σ) : c • f ∈ ptIntSer v σ := by
  intro α
  rw [map_smul, smul_eq_mul]
  exact Subring.mul_mem _ hc (hf α)
end ReciprocityTheory.ChartRestriction.G.Sh
