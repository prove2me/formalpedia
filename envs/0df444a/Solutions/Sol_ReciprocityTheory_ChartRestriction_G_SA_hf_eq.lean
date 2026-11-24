-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:25.375565+00:00
-- url     : https://prove2.me/submissions/94f90c25-e3de-491a-aceb-2a16d1468ed1

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
theorem _root_.solution (x y : ι → R) : hf σ J x y = (J *ᵥ (σ ∘ y)) ⬝ᵥ x := by
  simp only [hf, dotProduct, mulVec, Function.comp_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring
end ReciprocityTheory.ChartRestriction.G.SA
