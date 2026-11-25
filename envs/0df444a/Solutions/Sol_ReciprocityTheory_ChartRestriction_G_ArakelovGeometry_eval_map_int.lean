-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eval_map_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:44.653821+00:00
-- url     : https://prove2.me/submissions/ea15411a-5036-4700-a8ef-4099efc359e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {σ : Type*} (w : σ → ℂ) (p : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) p) = aeval w p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]
  congr 1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
