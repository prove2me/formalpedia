-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:05.895905+00:00
-- url     : https://prove2.me/submissions/74ab90fb-c634-41b2-a5c9-d5a220acdbde

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {n : ℕ} {c : MvPolynomial (Fin n) ℂ} {m : ℕ}
    (hc : c.IsHomogeneous m) (t : ℂ) (v : Fin n → ℂ) :
    eval (fun i => t * v i) c = t ^ m * eval v c := by
  conv_lhs => rw [c.as_sum]
  conv_rhs => rw [c.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have h1 := hc (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  simp only [mul_pow, Finsupp.prod_mul]
  rw [show (d.prod fun _ e => t ^ e) = t ^ m by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]]
  ring
end ReciprocityTheory.ChartRestriction.G.Geo
