-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:01.738455+00:00
-- url     : https://prove2.me/submissions/997c3850-b18e-4370-96a5-f99623777e91

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
theorem _root_.solution {σ : Type*} (s : σ) : (X s : MvPowerSeries σ C) ∈ ptIntSer v σ := by
  intro α
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _
end ReciprocityTheory.ChartRestriction.G.Sh
