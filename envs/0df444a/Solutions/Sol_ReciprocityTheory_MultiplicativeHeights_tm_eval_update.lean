-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_eval_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:22.410615+00:00
-- url     : https://prove2.me/submissions/08ff5b1b-7265-4e2d-9b88-636d87ac7e12

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
theorem _root_.solution (i : ι) (x : ι → ℂ) (z : ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (update x i z) f = (tmSlice i x f).eval z := by
  conv_lhs => rw [f.as_sum]
  simp only [tmSlice, map_sum, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, Function.update_self,
    Finsupp.erase_same, pow_zero, one_mul]
  have hp : ∏ j ∈ ({i}ᶜ : Finset ι), update x i z j ^ s j =
      ∏ j ∈ ({i}ᶜ : Finset ι), x j ^ (Finsupp.erase i s) j :=
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := by simpa using hj
      rw [Function.update_of_ne hji, Finsupp.erase_ne hji]
  rw [hp]
  ring
end ReciprocityTheory.MultiplicativeHeights
