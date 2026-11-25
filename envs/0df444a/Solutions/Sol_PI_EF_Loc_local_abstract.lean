-- Prove2me | solution 1 for PI.EF.Loc.local_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:24.142217+00:00
-- url     : https://prove2.me/submissions/7f427aea-65f9-4c1f-a6a1-a108b7b7eabb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract
import Theorems.Thm_PI_EF_Loc_locC_pos
import Theorems.Thm_PI_EF_Loc_core
import Theorems.Thm_PI_EF_Loc_order_eq_of_factor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology
namespace PI.EF.Loc
theorem _root_.solution (hDF : PI.DiscFactor) (hDL : PI.DiscLog) {r R' R : ℝ} (hr : 0 < r)
    (hrR' : r < R') (hR'R : R' < R) (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall s₀ R)) (hf0 : f s₀ ≠ 0) (hM : 0 ≤ M)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ({ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  have hR' : 0 < R' := hr.trans hrR'
  have hfd : DifferentiableOn ℂ f (closedBall s₀ R) := hf.differentiableOn
  obtain ⟨Z, m, h, hZ, -, hh, hh0, hfac⟩ := hDF f s₀ R R' hR' hR'R hfd hf0
  have hset : {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0} = (Z : Set ℂ) := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (hZ ρ).symm
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := by
    intro ρ hρ
    have hρR : ρ ∈ ball s₀ R := closedBall_subset_ball hR'R ((hZ ρ).1 hρ).1
    exact order_eq_of_factor hρ (isOpen_ball.mem_nhds hρR)
      (hf ρ (ball_subset_closedBall hρR)) (hh.mono ball_subset_closedBall)
      (hh0 ρ ((hZ ρ).1 hρ).1) fun z hz => hfac z (ball_subset_closedBall hz)
  refine ⟨by rw [hset]; exact Z.finite_toSet, ?_⟩
  intro s hs hfs
  have hsum : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) :=
    Finset.sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]
  rw [hset, finsum_mem_coe_finset, hsum]
  have hC : 0 < locC r R' R := locC_pos hr hrR' hR'R
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεC : 0 < ε / locC r R' R := div_pos hε hC
  have hM' : 0 < M + ε / locC r R' R := add_pos_of_nonneg_of_pos hM hεC
  have hb' : ∀ z ∈ closedBall s₀ R,
      ‖f z‖ ≤ Real.exp (M + ε / locC r R' R) * ‖f s₀‖ := fun z hz =>
    (hb z hz).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))
  have key := core hDL hr hrR' hR'R hM' hZ hh hh0 hfac hb' s hs hfs
  have hCε : locC r R' R * (ε / locC r R' R) = ε := by
    exact mul_div_cancel₀ ε hC.ne'
  calc _ ≤ locC r R' R * (M + ε / locC r R' R) := key
    _ = locC r R' R * M + ε := by rw [mul_add, hCε]
end PI.EF.Loc
