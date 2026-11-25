-- Prove2me | solution 1 for PI.QuotInvW.nu_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:52.759103+00:00
-- url     : https://prove2.me/submissions/34481dfe-e01f-4ed6-b273-696355b2287e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Theorems.Thm_PI_QuotInvW_inv_mul_of
import Theorems.Thm_PI_QuotInvW_measurableSet_mem
import Theorems.Thm_PI_QuotInvW_ae_mem_S
import Theorems.Thm_PI_QuotInvW_weil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution (h : QuotientSetting G S μG μS ν) : ν {x | Matrix.of x ∉ G} = 0 := by
  have hG := h.1
  have hS := h.2.1
  have hSG := h.2.2.1
  have hμG := h.2.2.2.1
  have hμS := h.2.2.2.2.1
  set C : Set (MtM m) := {x | Matrix.of x ∉ G} with hC
  have hCm : MeasurableSet C := (measurableSet_mem hG).compl
  have hW := weil h (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm, hμG.2.2.1] at hW
  have hle : ∀ x, C.indicator 1 x * μS Set.univ ≤ ∫⁻ s, C.indicator 1 (mm s x) ∂μS := by
    intro x
    by_cases hx : x ∈ C
    · have hae : ∀ᵐ s ∂μS, C.indicator (1 : MtM m → ℝ≥0∞) (mm s x) = 1 := by
        filter_upwards [ae_mem_S h] with s hs
        have : mm s x ∈ C := by
          intro hsx
          apply hx
          have h1 : (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) ∈ G :=
            hG.2.2.1 _ (hSG (hS.2.2.2 _ hs).1) _ hsx
          rwa [← Matrix.mul_assoc, inv_mul_of hS hs, Matrix.one_mul] at h1
        simp [Set.indicator_of_mem this]
      rw [lintegral_congr_ae hae]
      simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have h2 : ∫⁻ x, C.indicator 1 x * μS Set.univ ∂ν = 0 :=
    nonpos_iff_eq_zero.mp ((lintegral_mono hle).trans hW.symm.le)
  rw [lintegral_mul_const _ (measurable_one.indicator hCm), lintegral_indicator_one hCm,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd (Measure.measure_univ_eq_zero.mp h2) hμS.2.1
end PI.QuotInvW
