-- Prove2me | solution 1 for PI.OkpW.norm_le_one_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:27.97198+00:00
-- url     : https://prove2.me/submissions/addf84ee-74af-4a02-84e7-5e31e193682c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
namespace PI.OkpW
theorem _root_.solution {F R : Type*} [NormedField F] [IsUltrametricDist F] [CommRing R]
    [Algebra R F] (hR : ∀ r : R, ‖algebraMap R F r‖ ≤ 1) (δ : F) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨f, hf, hfe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one,
    one_mul] at hfe
  have h1 : δ ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hfe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ f.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ f.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R F (f.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ f.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ f.natDegree / ‖δ‖ < ‖δ‖ ^ f.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ f.natDegree‖ = ‖δ‖ ^ f.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith
end PI.OkpW
