-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_nat_poly_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:49.210648+00:00
-- url     : https://prove2.me/submissions/50530617-a0a0-4637-8b02-53404a3ae253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TchOfIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_exists_nat_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
theorem _root_.solution (y : PadicAlgCl l) (hy : ‖y‖ ≤ 1) :
    ∃ d : ℕ, ∃ c : ℕ → ℕ, ‖((X ^ d + ∑ i ∈ range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval
      (y : ℂ_[l]))‖ < 1 := by
  set P := minpoly ℚ_[l] y with hPdef
  have hint : IsIntegral ℚ_[l] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hmon : P.Monic := minpoly.monic hint
  have hcoef : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      have : spectralNorm ℚ_[l] (PadicAlgCl l) y = ‖y‖ := PadicAlgCl.spectralNorm_eq l y
      rw [spectralNorm] at this
      rw [hPdef, this]; exact hy
    exact (spectralValue_le_one_iff hmon).1 h1
  choose c hc using fun i => exists_nat_near l (P.coeff i) (hcoef i)
  refine ⟨P.natDegree, c, ?_⟩
  set z : ℂ_[l] := (y : ℂ_[l]) with hz
  have hP0 : aeval z P = 0 := by
    rw [hz, PadicComplex.coe_eq, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hPsum : aeval z P = z ^ P.natDegree +
      ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] (P.coeff i) * z ^ i := by
    conv_lhs => rw [hmon.as_sum]
    simp [map_add, map_sum, aeval_X, aeval_C]
  have he : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z =
      ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i := by
    have : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z =
        (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z -
          aeval z P := by rw [hP0, sub_zero]
    rw [this, hPsum]
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast, map_sub,
      map_natCast, sub_mul, sum_sub_distrib]
    ring
  have hz1 : ‖z‖ ≤ 1 := by rw [hz, PadicComplex.norm_extends]; exact hy
  rw [he]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le (range P.natDegree)
    (fun i => algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i)
  refine lt_of_le_of_lt hle ?_
  rw [norm_mul, norm_algebraMap', norm_pow, norm_sub_rev]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz1))
    (hc i)
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
