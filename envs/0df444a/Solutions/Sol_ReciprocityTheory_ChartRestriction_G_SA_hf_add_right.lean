-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hf_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:11.000879+00:00
-- url     : https://prove2.me/submissions/a80e74fe-baaf-475d-9be9-7a621a82f89f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (x y y' : ι → R) : hf σ J x (y + y') = hf σ J x y + hf σ J x y' := by
  simp only [hf, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring
end ReciprocityTheory.ChartRestriction.G.SA
