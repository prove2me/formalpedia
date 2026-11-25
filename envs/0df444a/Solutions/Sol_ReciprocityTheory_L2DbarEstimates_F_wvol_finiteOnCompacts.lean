-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.wvol_finiteOnCompacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:23.157956+00:00
-- url     : https://prove2.me/submissions/d156809b-84b7-418b-9c53-6b87468e558a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_isFiniteMeasureOnCompacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by
  have := vol_isFiniteMeasureOnCompacts n z hz
  refine ⟨fun K hK => ?_⟩
  have hc : ContinuousOn (fun x => Real.exp (-ph x)) K :=
    (Real.continuous_exp.comp hph.neg).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  unfold wvol
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂vol n z := by
        refine setLIntegral_mono' hK.measurableSet fun x hx => ENNReal.ofReal_le_ofReal ?_
        have h := hC x hx
        rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at h
    _ = ENNReal.ofReal C * vol n z K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
end ReciprocityTheory.L2DbarEstimates.F
