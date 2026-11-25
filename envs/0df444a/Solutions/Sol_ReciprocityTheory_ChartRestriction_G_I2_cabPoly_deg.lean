-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cabPoly_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:59.748033+00:00
-- url     : https://prove2.me/submissions/05ed36fd-c542-4e6d-9877-76669174a26e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (η : EuclideanSpace ℂ ι) (c : ℕ) : (cabPoly η c).totalDegree ≤ c := by
  unfold cabPoly
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have : (∑ i, MvPolynomial.C ((starRingEnd ℂ) (η i)) * MvPolynomial.X i : MvPolynomial ι ℂ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun i _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  calc c * _ ≤ c * 1 := Nat.mul_le_mul_left c this
    _ = c := mul_one c
end ReciprocityTheory.ChartRestriction.G.I2
