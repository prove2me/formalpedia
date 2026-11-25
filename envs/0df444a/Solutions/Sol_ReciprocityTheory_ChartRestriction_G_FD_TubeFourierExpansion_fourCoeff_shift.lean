-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.fourCoeff_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:23.69881+00:00
-- url     : https://prove2.me/submissions/db5b97f2-1e25-4b99-9ef1-d70072cf2b06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
theorem _root_.solution (g : (Fin n → ℂ) → ℂ) (y0 : Fin n → ℝ) (k : Fin n → ℤ) :
    fourCoeff (fun t => g (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff g y0 k := by
  have hx : ∀ (G Sx Sy : ℂ), G * cexp (-2 * Real.pi * I * Sx) =
      cexp (-2 * Real.pi * Sy) * (G * cexp (-2 * Real.pi * I * (Sx + Sy * I))) := by
    intro G Sx Sy
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    linear_combination (2 * (Real.pi : ℂ) * Sy) * Complex.I_sq
  have key : ∀ x : Fin n → ℝ,
      g ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) *
        cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I)) =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) *
        (g (fun j => (x j : ℂ) + (y0 j : ℂ) * I) *
          cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I))) := by
    intro x
    have hg : ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) =
        fun j => (x j : ℂ) + (y0 j : ℂ) * I := by
      funext j; simp
    have e1 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) =
        ∑ j, (k j : ℂ) * (x j : ℂ) := by simp
    have e2 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I) =
        ∑ j, (k j : ℂ) * (x j : ℂ) + (∑ j, (k j : ℂ) * (y0 j : ℂ)) * I := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have e3 : ((Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℝ) : ℂ) =
        cexp (-2 * Real.pi * ∑ j, (k j : ℂ) * (y0 j : ℂ)) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hg, e1, e2, e3]
    exact hx _ _ _
  unfold fourCoeff
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)
end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
