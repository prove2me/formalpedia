-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.secFun_map_intQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:37:33.983395+00:00
-- url     : https://prove2.me/submissions/dfd1e9b5-b935-471d-88dd-eedf07f67dbf

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
theorem _root_.solution (f : MvPolynomial (Ix κ) ℤ) (z : Ix κ → ℂ) :
    secFun (map (Int.castRingHom ℚ) f) z = eval z (map (Int.castRingHom ℂ) f) := by
  unfold secFun
  rw [MvPolynomial.map_map,
    show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
