-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.evalT_map_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:30.06942+00:00
-- url     : https://prove2.me/submissions/2b8a4ed0-5a02-4b7c-ad13-b357630be3a2

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
theorem _root_.solution (x : J → Ω) (b : MvPolynomial J ℚ) :
    evalT x (map (algebraMap ℚ ℂ) b) = (1 : ℂ) ⊗ₜ[ℚ] aeval x b := by
  unfold evalT
  rw [MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x (Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω) b
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
