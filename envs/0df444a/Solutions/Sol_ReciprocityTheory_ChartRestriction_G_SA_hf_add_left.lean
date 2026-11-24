-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hf_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:12.888314+00:00
-- url     : https://prove2.me/submissions/8d1f8ebd-5f60-469a-b116-f73f4c677cef

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
theorem _root_.solution (x x' y : ι → R) : hf σ J (x + x') y = hf σ J x y + hf σ J x' y := by
  simp only [hf, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring
end ReciprocityTheory.ChartRestriction.G.SA
