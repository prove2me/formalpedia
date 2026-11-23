-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.Phi_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.066564+00:00
-- url     : https://prove2.me/submissions/0961b88b-fe25-4635-94d0-dc321961c72b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs

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
theorem _root_.solution (z w : Fin (Fintype.card ι) → ℂ) : Phi e (z + w) = Phi e z + Phi e w := by
  simp only [Phi, Pi.add_apply, add_smul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.I2.DimC
