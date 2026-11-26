-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.eq_of_unit_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:14.51468+00:00
-- url     : https://prove2.me/submissions/ed74172f-7e99-4e1d-9537-f37a3ae68444

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
theorem _root_.solution {R : Type*} [CommRing R] (C : Rˣ) (h : C.val = 0) (a b : R) : a = b := by
  first
    | (have h0 : (1 : R) = 0 := by
         have := C.mul_inv
         rw [h, zero_mul] at this
         exact this.symm
       calc a = a * 1 := (mul_one a).symm
         _ = b * 1 := by rw [h0, mul_zero, mul_zero]
         _ = b := mul_one b)

