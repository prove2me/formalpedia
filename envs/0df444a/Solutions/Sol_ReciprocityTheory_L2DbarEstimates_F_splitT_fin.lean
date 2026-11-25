-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:16.571863+00:00
-- url     : https://prove2.me/submissions/dd9c2b48-5394-4126-bd66-6a4b28d152c8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  unfold wvol
  refine ⟨fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (Real.continuous_exp.comp hph.neg).continuousOn
  have hC' : ∀ x ∈ K, Real.exp (-ph x) ≤ C := fun x hx => by
    have h1 := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂vol n z :=
        setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal (hC' x hx)
    _ = ENNReal.ofReal C * vol n z K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
end ReciprocityTheory.L2DbarEstimates.F
