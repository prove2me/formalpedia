-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.int_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:56.320821+00:00
-- url     : https://prove2.me/submissions/63619cb3-5e50-4576-a794-f6616e758847

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
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
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {g : ℂ → ℂ} (hg : Measurable g) (C : ℝ) (h : ∀ z, z ≠ 0 → ‖g z‖ * (1 + ‖z‖) ^ 3 ≤ C) : Integrable g := by
  have h3 : Integrable fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ)) := integrable_one_add_norm (by simp; norm_num)
  refine (h3.const_mul C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
  have hp : 0 < (1 + ‖z‖) ^ 3 := by positivity
  rw [Real.rpow_neg (by positivity), show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact h z hz
end PositivityTheory.ThKG.Loc.Bump
