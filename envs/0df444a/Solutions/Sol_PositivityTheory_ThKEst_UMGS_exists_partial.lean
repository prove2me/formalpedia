-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.exists_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:56.429895+00:00
-- url     : https://prove2.me/submissions/8a9a912f-95b0-439f-ad43-05489f1ea259

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_pr_succ
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_tail
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_pr

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
omit [TopologicalSpace G] [ContinuousMul G]
namespace PositivityTheory.ThKEst.UMGS
theorem _root_.solution (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G)) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L)
    (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y) (n : WithTop ℕ∞) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, γ i ∈ L) →
    ∀ i, ∃ Z : (Fin k → ℝ) → ι → A, ContDiff ℝ n Z ∧ ∀ t, ∃ γ' ∈ L, Gn m γ' (Z t) ∧
      ∀ s, pr γ (update t i (t i + s)) = pr γ t * γ' (Multiplicative.ofAdd s) := by
  induction k with
  | zero => intro γ _ i; exact i.elim0
  | succ k ih =>
    intro γ hγ i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨Y, hY⟩ := hg _ (hγ 0)
      refine ⟨fun t w => m w (pr (fun i => γ i.succ) fun i => t i.succ)⁻¹ * Y w *
        m w (pr (fun i => γ i.succ) fun i => t i.succ), contDiff_pi.2 fun w => ?_, fun t =>
        ⟨_, hcj _ (hγ 0) _, hY.cj _, fun s => ?_⟩⟩
      · obtain ⟨h1, h2⟩ := contDiff_pr m n w k (fun i => γ i.succ) fun i => hg _ (hγ i.succ)
        exact ((h2.comp (contDiff_tail k n)).mul contDiff_const).mul (h1.comp (contDiff_tail k n))
      · simp only [pr_succ, cj_apply, update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true, update_of_ne,
          ofAdd_add, map_mul]
        group
    · obtain ⟨Z, hZ, h⟩ := ih (fun i => γ i.succ) (fun i => hγ i.succ) j
      refine ⟨fun t => Z fun i => t i.succ, hZ.comp (contDiff_tail k n), fun t => ?_⟩
      obtain ⟨γ', h1, h2, h3⟩ := h fun i => t i.succ
      refine ⟨γ', h1, h2, fun s => ?_⟩
      have e : (fun i : Fin k => update t j.succ (t j.succ + s) i.succ) =
          update (fun i : Fin k => t i.succ) j (t j.succ + s) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [pr_succ, pr_succ, e, h3, update_of_ne (Fin.succ_ne_zero j).symm, mul_assoc]
end PositivityTheory.ThKEst.UMGS
