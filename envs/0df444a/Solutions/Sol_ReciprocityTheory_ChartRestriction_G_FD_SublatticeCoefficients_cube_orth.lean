-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.cube_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:29.358837+00:00
-- url     : https://prove2.me/submissions/fff45a6c-4a1d-4c7a-ac14-26aded5f03ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_SublatticeCoefficients_ioc_orth

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
theorem _root_.solution {n : ℕ} (m : Fin n → ℤ) :
    ∫ t in Set.univ.pi (fun _ : Fin n => Set.Ioc (0 : ℝ) 1),
      cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) = if m = 0 then 1 else 0 := by
  have hprod : ∀ t : Fin n → ℝ, cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) =
      ∏ j, cexp (2 * Real.pi * I * (m j : ℂ) * (t j : ℂ)) := by
    intro t
    rw [Finset.mul_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by ring_nf
  simp_rw [hprod]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi fun _ => volume from rfl,
    Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (j : Fin n) (t : ℝ) => cexp (2 * Real.pi * I * (m j : ℂ) * (t : ℂ)))]
  simp_rw [ioc_orth]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra h; push Not at h; exact hm (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
end ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
