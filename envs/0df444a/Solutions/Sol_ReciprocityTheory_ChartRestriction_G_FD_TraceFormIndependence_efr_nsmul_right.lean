-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.efr_nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:25:57.547984+00:00
-- url     : https://prove2.me/submissions/a8307cff-614e-41b3-a100-35d5cba7ed10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
theorem _root_.solution (X : Data E r) (n : ℕ) (v w : X.Ψ → Fin r → ℂ) :
    efr X v ((n : ℂ) • w) = n * efr X v w := by
  unfold efr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : hermC τ.1 X.Gm (v τ) (((n : ℂ) • w) τ) = (n : ℂ) * hermC τ.1 X.Gm (v τ) (w τ) := by
    simp only [hermC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    ring
  rw [h, mul_left_comm]
  have e : ((n : ℂ) * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ))).re =
      (n : ℝ) * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ)).re := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [e]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
