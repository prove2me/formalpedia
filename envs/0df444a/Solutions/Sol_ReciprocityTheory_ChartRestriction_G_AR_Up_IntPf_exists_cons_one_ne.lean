-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.exists_cons_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:14.098098+00:00
-- url     : https://prove2.me/submissions/e639629a-b305-4189-8166-8e51f813126f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_eval_mul_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
theorem _root_.solution {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    {G : MvPolynomial (Fin (n + 1)) K} (hG : G.IsHomogeneous m) (h0 : G ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) G ≠ 0 := by
  by_contra! h
  apply h0
  have hX : (X 0 * G : MvPolynomial (Fin (n + 1)) K) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [map_mul, eval_X, map_zero]
    by_cases hp : p 0 = 0
    · rw [hp, zero_mul]
    · have hq : p = fun i => (Fin.cons 1 (fun k => p k.succ / p 0) : Fin (n + 1) → K) i * p 0 := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp
        · simp [div_mul_cancel₀ _ hp]
      have : eval p G = 0 := by
        rw [hq]
        rw [eval_mul_homog _ _ hG, h, mul_zero]
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
