-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.pr_bet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:12.028313+00:00
-- url     : https://prove2.me/submissions/5e85da83-afab-4fa4-b802-5f3caa623864

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
omit [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (ξ : K → ι → n → ℂ) (k : K) (η : XS (ι × n)) (t : ι → ℂ) : pr (bet ξ (k, η)) t = ⟪η, pim ξ (k, t)⟫ := by
  simp only [pr, bet, pim, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_mul, Complex.re_sum, Finset.mul_sum, Complex.inner]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  simp; ring
end PositivityTheory.ThKG.Loc.Bump
