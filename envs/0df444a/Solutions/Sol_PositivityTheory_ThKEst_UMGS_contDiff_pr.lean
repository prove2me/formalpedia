-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.contDiff_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:19.144996+00:00
-- url     : https://prove2.me/submissions/2209cfaa-daab-4b3a-9227-14f6521947cc

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_pr_succ
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_pr_zero
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_exp_smul
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_tail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.UMGS
open Filter Topology Function
variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]
omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι]
namespace PositivityTheory.ThKEst.UMGS
theorem _root_.solution (m : ι → G →* A) (n : WithTop ℕ∞) (w : ι) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G),
    (∀ i, ∃ Y, Gn m (γ i) Y) → ContDiff ℝ n (fun t => m w (pr γ t)) ∧ ContDiff ℝ n (fun t => m w (pr γ t)⁻¹) := by
  induction k with
  | zero => intro γ _; simp only [pr_zero]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro γ hγ
    obtain ⟨h1, h2⟩ := ih (fun i => γ i.succ) fun i => hγ i.succ
    obtain ⟨Y, hY⟩ := hγ 0
    simp only [pr_succ, mul_inv_rev, map_mul, ← map_inv, ← ofAdd_neg, hY w]
    exact ⟨((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ ℝ 0)).mul (h1.comp (contDiff_tail k n)),
      (h2.comp (contDiff_tail k n)).mul ((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ ℝ 0).neg)⟩
end PositivityTheory.ThKEst.UMGS
