-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.prp_pim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:19.434303+00:00
-- url     : https://prove2.me/submissions/95b40355-c6d1-4796-9858-cb1a3051c6d6

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_exists_lb
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
theorem _root_.solution [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) (hne : ∀ k w, ξ k w ≠ 0) (k₁ : K) :
    Prp (pim ξ) (pim ξ (k₁, 1)) := by
  refine ⟨by unfold pim; fun_prop, ⟨_, rfl⟩, ?_⟩
  obtain ⟨m, hm, hb⟩ := exists_lb (g := fun k w => ‖ξ k w‖) (fun w => by fun_prop) fun k w => norm_pos_iff.2 (hne k w)
  refine ⟨m, {p | ∀ w, m / 2 ≤ ‖p.2 w‖ * ‖ξ p.1 w‖} ∩ univ ×ˢ Metric.closedBall 0 ((‖ξ k₁‖ + m) / m), hm, ?_, ?_, fun p hp => ?_⟩
  · refine IsCompact.inter_left (isCompact_univ.prod (isCompact_closedBall _ _)) ?_
    simp only [setOf_forall]
    exact isClosed_iInter fun w => isClosed_le continuous_const (by fun_prop)
  · intro p hp w h0
    have := hp.1 w
    rw [h0, norm_zero, zero_mul] at this
    linarith
  · have key : ∀ w, ‖p.2 w • ξ p.1 w - ξ k₁ w‖ ≤ m / 2 := fun w => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      have h1 := (PiLp.norm_apply_le (pim ξ p - pim ξ (k₁, 1)) (w, i)).trans ((dist_eq_norm _ _).symm.le.trans hp)
      have h2 : (pim ξ p - pim ξ (k₁, 1)) (w, i) = 2 * (p.2 w • ξ p.1 w - ξ k₁ w) i := by simp [pim]; ring
      rw [h2, norm_mul, Complex.norm_ofNat] at h1
      linarith
    refine ⟨fun w => ?_, trivial, ?_⟩
    · have := norm_sub_norm_le (ξ k₁ w) (p.2 w • ξ p.1 w)
      rw [norm_sub_rev, norm_smul] at this
      linarith [key w, hb k₁ w]
    · rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
      have := norm_sub_norm_le (p.2 w • ξ p.1 w) (ξ k₁ w)
      rw [norm_smul] at this
      rw [le_div_iff₀ hm]
      nlinarith [key w, hb p.1 w, norm_le_pi_norm (ξ k₁) w, norm_nonneg (p.2 w)]
end PositivityTheory.ThKG.Loc.Bump
