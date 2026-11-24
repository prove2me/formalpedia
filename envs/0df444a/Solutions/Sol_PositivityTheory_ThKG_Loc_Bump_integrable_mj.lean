-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.integrable_mj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:38.891802+00:00
-- url     : https://prove2.me/submissions/6b200c4e-0dda-437d-bbe7-7a3a08129dbc

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
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution : Integrable (mj : (ι → ℂ) → ℝ) := by
  have h : Integrable fun z : ι → ℂ => (1 + ‖z‖) ^ (-((Module.finrank ℝ (ι → ℂ) + 1 : ℕ) : ℝ)) :=
    integrable_one_add_norm (by push_cast; linarith)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [mj]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
end PositivityTheory.ThKG.Loc.Bump
