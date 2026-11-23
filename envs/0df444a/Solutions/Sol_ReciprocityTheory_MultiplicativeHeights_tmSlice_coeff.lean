-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tmSlice_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:21.038819+00:00
-- url     : https://prove2.me/submissions/e22781da-20ad-4b84-8a35-9f4e74a7b8e5

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) (k : ℕ) :
    (tmSlice i x f).coeff k = MvPolynomial.eval x (coeffIn i k f) := by
  simp only [tmSlice, coeffIn, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
