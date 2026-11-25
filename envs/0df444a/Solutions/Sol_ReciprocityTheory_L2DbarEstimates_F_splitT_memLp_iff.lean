-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_memLp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:31:42.931164+00:00
-- url     : https://prove2.me/submissions/e21287aa-b894-44a3-be13-0ce1701669a4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_meas_dens
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] (ph : M → ℝ) (hph : Continuous ph)
    (u : M → E) (hu : AEStronglyMeasurable u (vol n z)) :
    MemLp u 2 (wvol n z ph) ↔
      ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z < ⊤ := by
  have hac : wvol n z ph ≪ vol n z := withDensity_absolutelyContinuous _ _
  have hu' : AEStronglyMeasurable u (wvol n z ph) := hu.mono_ac hac
  have he : ∀ x, (ENNReal.ofReal (Real.exp (-ph x))).toReal = Real.exp (-ph x) :=
    fun x => ENNReal.toReal_ofReal (Real.exp_nonneg _)
  have hm : AEStronglyMeasurable (fun x => ‖u x‖ ^ 2 * Real.exp (-ph x)) (vol n z) :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp hph.neg).aestronglyMeasurable
  have h0 : (0 : M → ℝ) ≤ᵐ[vol n z] fun x => ‖u x‖ ^ 2 * Real.exp (-ph x) :=
    Filter.Eventually.of_forall fun x => by
      show (0 : ℝ) ≤ _
      positivity
  rw [memLp_two_iff_integrable_sq_norm hu']
  unfold wvol
  rw [integrable_withDensity_iff (splitT_meas_dens ph hph)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [he]
  constructor
  · intro hI
    exact (hasFiniteIntegral_iff_ofReal h0).1 hI.2
  · intro hI
    exact ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 hI⟩
end ReciprocityTheory.L2DbarEstimates.F
