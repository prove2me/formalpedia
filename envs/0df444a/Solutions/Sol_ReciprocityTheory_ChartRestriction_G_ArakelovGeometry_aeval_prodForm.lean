-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_prodForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:15.755858+00:00
-- url     : https://prove2.me/submissions/0691cbc0-5b5c-41d2-9308-312b4f51a0a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ)
    (h : MvPolynomial (Ix κ) ℤ) :
    aeval x (prodForm e a h) = (∏ t, (x ∘ e) t ^ a t) * aeval x h := by
  rw [prodForm, map_mul, aeval_rename]
  simp [monoZ, aeval_monomial, Finsupp.prod_fintype]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
