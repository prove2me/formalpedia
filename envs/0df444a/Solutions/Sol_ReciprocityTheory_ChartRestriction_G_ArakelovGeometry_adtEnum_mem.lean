-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adtEnum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:52.397797+00:00
-- url     : https://prove2.me/submissions/d10e42eb-ab5c-46b9-a204-4683f21e778f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD

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
theorem _root_.solution (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) :
    adtEnum D N i ∈ Finset.Nat.antidiagonalTuple (D + 1) N :=
  ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm i).2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
