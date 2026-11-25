-- Prove2me | solution 1 for PI.QD.quadratic_intCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:06:41.080419+00:00
-- url     : https://prove2.me/submissions/c0e6ee72-8650-4439-bdc0-0568bd78ce50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuadDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadDiffOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.QD
open NumberField Polynomial
namespace PI.QD
theorem _root_.solution : IntCoeffs := by
  unfold IntCoeffs
  intro K _ _ d θ x y hsq hd4 hθ hint
  have hd : (0 : ℚ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  by_cases hy : y = 0
  · subst hy
    have h1 : IsIntegral ℤ (algebraMap ℚ K x) := by
      rw [eq_ratCast]
      simpa using hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h1)
    rw [eq_intCast] at hn
    subst hn
    exact ⟨⟨2 * n, by push_cast; ring⟩, ⟨n ^ 2, by push_cast; ring⟩⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℚ, p = X ^ 2 - C (2 * x) * X + C (x ^ 2 + d * y ^ 2) := ⟨_, rfl⟩
  have hmonic : p.Monic := by
    rw [hp]
    monicity!
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree!
  have haeval : aeval ((x : K) + (y : K) * θ) p = 0 := by
    rw [hp]
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, eq_ratCast]
    push_cast
    linear_combination ((y : K)) ^ 2 * hθ
  have hirr : Irreducible p := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    rw [mem_roots hmonic.ne_zero, IsRoot, hp] at hr
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (r - x), mul_pos hd hy2]
  have hmin : p = minpoly ℚ ((x : K) + (y : K) * θ) := minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have hg := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hc : ∀ i, p.coeff i = ((minpoly ℤ ((x : K) + (y : K) * θ)).coeff i : ℚ) := by
    intro i
    rw [hmin, hg, Polynomial.coeff_map, eq_intCast]
  have h1 : p.coeff 1 = -(2 * x) := by
    rw [hp]
    simp
    rw [← C_pow, ← C_pow, coeff_C, coeff_C]
    simp
  have h0 : p.coeff 0 = x ^ 2 + d * y ^ 2 := by
    rw [hp]
    simp
    rw [← C_pow, ← C_pow, coeff_C, coeff_C]
    simp
  refine ⟨⟨-(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 1, ?_⟩, ⟨(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 0, ?_⟩⟩
  · push_cast
    rw [← hc, h1]
    ring
  · rw [← hc, h0]
end PI.QD
