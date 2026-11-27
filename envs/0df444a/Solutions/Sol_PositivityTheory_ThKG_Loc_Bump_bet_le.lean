-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.bet_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:29.466003+00:00
-- url     : https://prove2.me/submissions/631e2d9f-9de5-4c70-b195-0144f4c16bdf

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) : ∃ D : ℝ, ∀ k η, ‖bet ξ (k, η)‖ ≤ D * ‖η‖ := by
  obtain ⟨C, hC⟩ := (isCompact_range h).isBounded.exists_norm_le
  refine ⟨Fintype.card n * |C|, fun k η => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖ξ k w i‖ ≤ |C| := ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ w)).trans ((hC _ ⟨k, rfl⟩).trans (le_abs_self C))
  exact mul_le_mul h1 (PiLp.norm_apply_le η (w, i)) (norm_nonneg _) (abs_nonneg _)
end PositivityTheory.ThKG.Loc.Bump
