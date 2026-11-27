-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.rationalWeight_eq_mul_norm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:24.321079+00:00
-- url     : https://prove2.me/submissions/73072fca-f3d3-4534-a683-7b34ec9843ce

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
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
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : r0 κ e x = r0 κ 0 x * ((nm x : ℝ) : ℂ) ^ e := by
  simp only [r0, nm]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring
end PositivityTheory.ThKG.Loc.Bump
