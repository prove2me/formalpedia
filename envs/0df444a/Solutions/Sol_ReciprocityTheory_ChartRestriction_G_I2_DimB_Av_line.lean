-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.Av_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:38:59.375061+00:00
-- url     : https://prove2.me/submissions/010e1495-1bc3-41ce-948c-06ecdf2028b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_continuous_rl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Av_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_line_cauchy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ubox_sub_Icc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution (Ψ : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ Ψ) (hp : IPer Ψ) (w : Fin k → ℂ)
    (l : Fin k) (y : ℝ) : Av Ψ (w + ((y : ℂ) * I) • Pi.single l 1) = Av Ψ w := by
  have hc := hd.continuous
  have hp1 : ∀ z, Ψ (z + Pi.single l 1) = Ψ z := fun z => by
    have := hp (Pi.single l 1) z
    have e : iz (Pi.single l (1 : ℤ)) = (Pi.single l 1 : Fin k → ℂ) := by
      funext i; simp [iz, Pi.single_apply]
    rwa [e] at this
  have avg : ∀ v, Av Ψ v = ∫ t in ubox k, ∫ x in (0:ℝ)..1, Ψ (rl t + v + (x : ℂ) • Pi.single l 1) := by
    intro v
    have e2 : ∀ x : ℝ, rl (Pi.single l x) = (x : ℂ) • (Pi.single l 1 : Fin k → ℂ) := fun x => by
      funext i; simp [rl, Pi.single_apply]; split_ifs <;> simp
    have e1 : Av Ψ v = ∫ x in (0:ℝ)..1, Av Ψ (v + (x : ℂ) • Pi.single l 1) := by
      simp_rw [← e2, Av_real Ψ hc hp]; simp
    rw [e1]
    simp only [Av]
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [integral_integral_swap]
    · congr 1; funext t; rw [intervalIntegral.integral_of_le zero_le_one]
      congr 1; funext x; rw [add_assoc]
    · rw [Measure.prod_restrict]
      refine (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_).mono_set
        (Set.prod_mono Ioc_subset_Icc_self ubox_sub_Icc)
      refine Continuous.continuousOn ?_
      exact hc.comp ((continuous_rl.comp continuous_snd).add
        (continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const)))
  rw [avg, avg]
  congr 1; funext t
  rw [line_cauchy Ψ hd l hp1 (rl t + w) y]
  congr 1; funext x; rw [← add_assoc]
end ReciprocityTheory.ChartRestriction.G.I2.DimB
