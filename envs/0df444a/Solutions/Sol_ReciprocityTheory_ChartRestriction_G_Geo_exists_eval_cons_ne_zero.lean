-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_eval_cons_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:47.611296+00:00
-- url     : https://prove2.me/submissions/3debfc8c-9f4b-4c41-a6eb-c31cf080c3c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_isHomogeneous

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
theorem _root_.solution {n : ℕ} {c : MvPolynomial (Fin (n + 1)) ℂ} {m : ℕ}
    (hc0 : c ≠ 0) (hc : c.IsHomogeneous m) : ∃ y : Fin n → ℂ, eval (Fin.cons 1 y) c ≠ 0 := by
  by_contra h
  push_neg at h
  apply hc0
  have hX : (X 0 : MvPolynomial (Fin (n + 1)) ℂ) * c = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · have hxe : x = fun i => x 0 * (Fin.cons 1 (fun j => x j.succ / x 0) : Fin (n + 1) → ℂ) i := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rw [Fin.cons_succ, mul_div_left_comm, div_self hx, mul_one]
      have hx0 : eval x c = 0 := by
        rw [hxe, eval_smul_of_isHomogeneous hc (x 0) (Fin.cons 1 (fun j => x j.succ / x 0)), h,
          mul_zero]
      rw [hx0, mul_zero]
  rcases mul_eq_zero.mp hX with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · exact h0
end ReciprocityTheory.ChartRestriction.G.Geo
