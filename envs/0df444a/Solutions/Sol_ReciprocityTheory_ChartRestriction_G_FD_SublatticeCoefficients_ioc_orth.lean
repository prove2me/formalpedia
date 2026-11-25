-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.ioc_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:28.286034+00:00
-- url     : https://prove2.me/submissions/a20d6ddf-1f62-45ff-9162-e981f2e8452b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
open NumberField Complex MeasureTheory ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
  ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
namespace ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
theorem _root_.solution (m : ℤ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, cexp (2 * Real.pi * I * (m : ℂ) * (t : ℂ)) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm; simp
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hc : (2 * Real.pi * I * (m : ℂ)) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, Complex.I_ne_zero, hm']
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * Real.pi * I * (m : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * I * (m : ℂ) * ((1 : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]
    simp
end ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
