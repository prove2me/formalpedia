-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.Dec.bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:38.536115+00:00
-- url     : https://prove2.me/submissions/2c857faa-c43e-4aa0-aaaa-40ebce444c3c

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
namespace Dec
theorem _root_.solution {a : K × (ι → ℂ) → ℂ} (ha : Dec a) (M : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k x b : _,
    ‖a (k, x + b)‖ * (1 + ‖x‖) ^ M ≤ C * (1 + ‖b‖) ^ N * mj x := by
  obtain ⟨C, hC⟩ := ha (M + (Module.finrank ℝ (ι → ℂ) + 1))
  refine ⟨max C 0, M + (Module.finrank ℝ (ι → ℂ) + 1), le_max_right _ _, fun k x b => ?_⟩
  rw [mj, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_assoc, ← pow_add]
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x + b‖) * (1 + ‖b‖) := by
    have : ‖x‖ ≤ ‖x + b‖ + ‖b‖ := by simpa using norm_sub_le (x + b) b
    nlinarith [norm_nonneg (x + b), norm_nonneg b]
  calc _ ≤ ‖a (k, x + b)‖ * ((1 + ‖x + b‖) * (1 + ‖b‖)) ^ (M + (Module.finrank ℝ (ι → ℂ) + 1)) := by gcongr
    _ = ‖a (k, x + b)‖ * (1 + ‖x + b‖) ^ (M + (Module.finrank ℝ (ι → ℂ) + 1)) * (1 + ‖b‖) ^ (M + (Module.finrank ℝ (ι → ℂ) + 1)) := by
        rw [mul_pow, mul_assoc]
    _ ≤ _ := by gcongr; exact (hC k _).trans (le_max_left _ _)
end Dec
end PositivityTheory.ThKG.Loc.Bump
