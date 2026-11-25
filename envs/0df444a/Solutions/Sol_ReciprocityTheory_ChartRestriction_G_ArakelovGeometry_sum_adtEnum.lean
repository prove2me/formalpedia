-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_adtEnum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:08.990701+00:00
-- url     : https://prove2.me/submissions/662d675f-2d7f-42f5-8740-5681164161ef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA

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
open scoped ComplexOrder
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {M : Type*} [AddCommMonoid M] (D N : ℕ) (f : (Fin (D + 1) → ℕ) → M) :
    ∑ i, f (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, f a := by
  exact (Fintype.sum_equiv (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm _
    (fun x => f x.1) fun _ => rfl).trans (Finset.sum_coe_sort _ f)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
