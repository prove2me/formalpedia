-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.Phi_tau
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:30.897793+00:00
-- url     : https://prove2.me/submissions/49ec3ca6-822d-4386-a6c6-06ceddfe5290

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_eb_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (j : Fin (Fintype.card ι)) : Phi e (tau e f hee hef j) = f j := by
  simp only [Phi, tau]
  conv_rhs => rw [← (eb e f hee hef).sum_repr (f j)]
  simp only [eb_apply]
end ReciprocityTheory.ChartRestriction.G.I2.DimC
