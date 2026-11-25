-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isReduced_tensor_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:00.902919+00:00
-- url     : https://prove2.me/submissions/c6790b07-d0bd-4842-b3ea-c827221c44b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (Ω E : Type*) [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : IsReduced (E ⊗[ℚ] Ω) := by
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : IsReduced (Ω ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[ℚ] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm ℚ E Ω).toRingHom
    (Algebra.TensorProduct.comm ℚ E Ω).injective
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
