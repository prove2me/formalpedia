-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Specmeas.exists_measure_of_positive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:50.852321+00:00
-- url     : https://prove2.me/submissions/42c08eeb-f357-4a08-8e17-466c82464d76

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_ofR_add
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_ofR_sub
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_ofR_smul
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_eq_ofR_re_add_im
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_nonneg_ofR
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_ofR_eq_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
namespace PositivityTheory.Rg.BcB.E2.P.Specmeas
theorem _root_.solution (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ.Regular ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  let Λr : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun g := (Λ (ofR g.toContinuousMap)).re
    map_add' g g' := by
      have : (g + g').toContinuousMap = g.toContinuousMap + g'.toContinuousMap := rfl
      rw [this, ofR_add, map_add, Complex.add_re]
    map_smul' c g := by
      have : (c • g).toContinuousMap = c • g.toContinuousMap := rfl
      rw [this, ofR_smul, map_smul]; simp
    monotone' g g' hgg' := by
      have h := nonneg_ofR Λ hΛ (g := g'.toContinuousMap - g.toContinuousMap)
        (fun x => sub_nonneg.2 (hgg' x))
      rw [ofR_sub, map_sub, Complex.le_def] at h
      have := h.1
      simp only [Complex.zero_re, Complex.sub_re] at this
      linarith }
  refine ⟨RealRMK.rieszMeasure Λr, inferInstance, inferInstance, fun f => ?_⟩
  have key : ∀ g : C(X, ℝ), Λ (ofR g) = ((∫ x, g x ∂(RealRMK.rieszMeasure Λr) : ℝ) : ℂ) := by
    intro g
    have := RealRMK.integral_rieszMeasure Λr (CompactlySupportedContinuousMap.continuousMapEquiv g)
    rw [ofR_eq_re Λ hΛ g]
    congr 1
    exact this.symm
  have hint : Integrable (fun x => f x) (RealRMK.rieszMeasure Λr) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  conv_lhs => rw [eq_ofR_re_add_im f]
  rw [map_add, map_smul, key, key, ← integral_re_add_im hint, smul_eq_mul, mul_comm]
  rfl
end PositivityTheory.Rg.BcB.E2.P.Specmeas
