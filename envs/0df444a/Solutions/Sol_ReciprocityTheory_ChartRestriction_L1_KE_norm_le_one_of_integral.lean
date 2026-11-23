-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:11.494615+00:00
-- url     : https://prove2.me/submissions/b5ebde04-bf3f-461a-9b25-eb68e8aa46d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {K R : Type*} [NormedField K] [IsUltrametricDist K] [CommRing R]
    [Algebra R K] (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (δ : K) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨p, hp, hpe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpe
  have h1 : δ ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hpe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ p.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R K (p.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ p.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ p.natDegree / ‖δ‖ < ‖δ‖ ^ p.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ p.natDegree‖ = ‖δ‖ ^ p.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith
end ReciprocityTheory.ChartRestriction.L1.KE
