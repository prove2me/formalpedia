-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paMono_smul_paT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:50.850995+00:00
-- url     : https://prove2.me/submissions/e8c63e8f-700b-4a4c-9efa-8bf7774a14a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paT_apply

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
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (α : ι →₀ ℕ) (t : ℝ) (z : EuclideanSpace ℂ (Fin (Fintype.card ι))) :
    paMono α (t • paT z) = (t : ℂ) ^ α.degree *
      paMono (Finsupp.equivMapDomain (Fintype.equivFin ι) α) z := by
  simp only [paMono, paPF, MvPolynomial.eval_monomial, one_mul, Finsupp.prod_equivMapDomain,
    PiLp.smul_apply, paT_apply, Complex.real_smul, mul_pow]
  rw [Finsupp.prod, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl
end ReciprocityTheory.ChartRestriction.G.I2
