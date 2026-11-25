-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eval_prodForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:10.459891+00:00
-- url     : https://prove2.me/submissions/9af6604f-8efb-461e-8e78-f285fe8ded67

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
theorem _root_.solution (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ) (h : MvPolynomial (Ix κ) ℤ)
    (z : Ix κ → ℂ) :
    eval z (map (Int.castRingHom ℂ) (prodForm e a h)) =
      monoC a (z ∘ e) * eval z (map (Int.castRingHom ℂ) h) := by
  rw [prodForm, map_mul, map_mul, map_rename, eval_rename]
  simp [monoZ, map_monomial, eval_monomial, monoC, Finsupp.prod_fintype]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
