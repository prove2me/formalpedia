-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.locL2_sub_weightedL2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:14.071322+00:00
-- url     : https://prove2.me/submissions/270eef7f-10a5-4136-855c-1abc076883fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_norm_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_WeakAdj_sub
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
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (F0 : M → ℂ) (hF0 : Continuous F0) (u : Lp ℂ 2 (wvol n z ph)) :
    LocalL2Isometry (vol n z) (fun x => F0 x - u x) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hph' := gm_cont_of_smoothR n z hz ph hph
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph'.measurable.neg)
  have hne : ∀ᵐ x ∂vol n z, ENNReal.ofReal (Real.exp (-ph x)) ≠ 0 :=
    Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hac : vol n z ≪ wvol n z ph := by
    rw [wvol]
    first
      | exact withDensity_absolutelyContinuous' hm.aemeasurable hne
      | exact withDensity_absolutelyContinuous' hm hne
  have hu : AEStronglyMeasurable (fun x => u x) (vol n z) := (Lp.aestronglyMeasurable u).mono_ac hac
  have hmeas : AEStronglyMeasurable (fun x => F0 x - u x) (vol n z) :=
    hF0.aestronglyMeasurable.sub hu
  refine ⟨hmeas, fun C hC => ?_⟩
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF0.continuousOn
  obtain ⟨M0, hM0⟩ := hC.exists_bound_of_continuousOn hph'.continuousOn
  have hCfin : vol n z C < ⊤ := hC.measure_lt_top
  haveI : IsFiniteMeasure ((vol n z).restrict C) := by
    first
      | exact isFiniteMeasure_restrict.2 hCfin.ne
      | exact ⟨by rw [Measure.restrict_apply_univ]; exact hCfin⟩
  have hF0C : MemLp F0 2 ((vol n z).restrict C) :=
    MemLp.of_bound hF0.aestronglyMeasurable.restrict B
      ((ae_restrict_iff' hC.measurableSet).2 (Eventually.of_forall hB))
  have hfin : ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n z ph < ⊤ := by
    rw [← gm_norm_sq u]
    exact ENNReal.ofReal_lt_top
  have hw : ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n z ph =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ) ∂vol n z :=
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  have hsetle : ∫⁻ x in C, ENNReal.ofReal (Real.exp M0) *
        (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp M0) *
        (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z := by
    first
      | exact setLIntegral_le_lintegral _ _
      | exact lintegral_mono' Measure.restrict_le_self le_rfl
  have huC : MemLp (fun x => u x) 2 ((vol n z).restrict C) := by
    rw [gm_memLp_two_iff _ hu.restrict]
    calc ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(vol n z).restrict C
        ≤ ∫⁻ x in C, ENNReal.ofReal (Real.exp M0) *
            (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z := by
          refine lintegral_mono_ae ((ae_restrict_iff' hC.measurableSet).2
            (Eventually.of_forall fun x hx => ?_))
          have hle : ph x ≤ M0 :=
            le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hM0 x hx)
          have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp M0) * ENNReal.ofReal (Real.exp (-ph x)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by linarith))
          calc ‖u x‖ₑ ^ (2:ℝ) = 1 * ‖u x‖ₑ ^ (2:ℝ) := (one_mul _).symm
            _ ≤ (ENNReal.ofReal (Real.exp M0) * ENNReal.ofReal (Real.exp (-ph x))) *
                ‖u x‖ₑ ^ (2:ℝ) := by gcongr
            _ = _ := mul_assoc _ _ _
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp M0) *
            (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z := hsetle
      _ = ENNReal.ofReal (Real.exp M0) * ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n z ph := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hw]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hsub := hF0C.sub huC
  rw [gm_memLp_two_iff _ hsub.1] at hsub
  have e2 : ∀ x, ‖F0 x - u x‖ₑ ^ (2:ℝ) = ‖F0 x - u x‖ₑ ^ 2 := by
    intro x
    first
      | exact ENNReal.rpow_two _
      | exact_mod_cast ENNReal.rpow_natCast _ 2
  simpa [e2] using hsub
end ReciprocityTheory.L2DbarEstimates.F
