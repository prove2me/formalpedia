-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.Dec.integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:23.769543+00:00
-- url     : https://prove2.me/submissions/eadfaceb-b7da-4621-a738-32eff1164bb4

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_Dec_bound
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_mj
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
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
omit [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
namespace Dec
theorem _root_.solution {a : K × (ι → ℂ) → ℂ} (hd : Dec a) (k : K) (ha : Continuous fun x => a (k, x)) : Integrable fun x => a (k, x) := by
  obtain ⟨C, N, -, hC⟩ := hd.bound 0
  exact (integrable_mj.const_mul C).mono' ha.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hC k x 0)
end Dec
end PositivityTheory.ThKG.Loc.Bump
