-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.evalT_map_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:25.582557+00:00
-- url     : https://prove2.me/submissions/f7652116-6ab7-4f80-8b43-e45e8b6c79ff

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
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : J → Ω) (f : MvPolynomial J ℤ) :
    evalT x (map (Int.castRingHom ℂ) f) = (1 : ℂ) ⊗ₜ[ℚ] aeval x f := by
  unfold evalT
  rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x
    ((Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω).restrictScalars ℤ) f
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
