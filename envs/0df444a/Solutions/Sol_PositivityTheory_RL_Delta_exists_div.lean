-- Prove2me | solution 1 for PositivityTheory.RL.Delta.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:40.567093+00:00
-- url     : https://prove2.me/submissions/e5b175f3-69f3-46a7-a4ed-62cd014a8498

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
import Theorems.Thm_PositivityTheory_RL_Delta_hadamard_lemma
import Theorems.Thm_PositivityTheory_RL_Delta_exists_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Delta
open Complex
open scoped Real ContDiff
namespace PositivityTheory.RL.Delta
theorem _root_.solution (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := by
  obtain ⟨q, hq, hq'⟩ := exists_quot
  obtain ⟨h, hh, hh'⟩ := hadamard_lemma n f (f.smooth ⊤) h0
  have hK : IsCompact (tsupport (f : (Fin n → ℝ) → ℂ)) :=
    (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (hf.trans Metric.ball_subset_closedBall)
  obtain ⟨r, hr, hr'⟩ := exists_lt_subset_ball (isClosed_tsupport _) hf
  set r' : ℝ := max r (1 / 2) with hr'def
  have hr1 : r' < 1 := max_lt hr (by norm_num)
  have hr0 : 0 < r' := lt_max_of_lt_right (by norm_num)
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨r', (r' + 1) / 2, hr0, by linarith⟩
  have hbs : tsupport (b : (Fin n → ℝ) → ℝ) ⊆ Metric.ball 0 1 := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by show (r' + 1) / 2 < 1; linarith)
  have hcoord : ∀ (i : Fin n), ∀ x ∈ Metric.ball (0 : Fin n → ℝ) 1, x i ∈ Metric.ball (0 : ℝ) 1 := by
    intro i x hx
    rw [mem_ball_zero_iff] at hx ⊢
    exact (norm_le_pi_norm x i).trans_lt hx
  have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) := by
    intro i
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_of_tsupport fun x hx => ?_
    rw [contMDiffAt_iff_contDiffAt]
    have hx' : x ∈ Metric.ball (0 : Fin n → ℝ) 1 := hbs (tsupport_smul_subset_left _ _ hx)
    refine b.contDiff.contDiffAt.smul (ContDiffAt.mul ?_ (hh i).contDiffAt)
    exact ContDiffAt.comp x (g := q) (f := fun x : Fin n → ℝ => x i)
      (hq.contDiffAt (Metric.isOpen_ball.mem_nhds (hcoord i x hx'))) (contDiffAt_apply ℝ ℝ i x)
  have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) :=
    fun i => b.hasCompactSupport.smul_right
  refine ⟨fun i => (hcs i).toSchwartzMap (hsm i), hcs, fun x => ?_⟩
  show f x = ∑ i, (cexp (2 * π * I * x i) - 1) * (b x • (q (x i) * h i x))
  have hb : f x = b x • f x := by
    by_cases hx : x ∈ tsupport (f : (Fin n → ℝ) → ℂ)
    · rw [b.one_of_mem_closedBall, one_smul]
      exact Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_max_left _ _) (hr' hx))
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  by_cases hx : x ∈ Metric.ball (0 : Fin n → ℝ) 1
  · rw [hb, hh' x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, ← mul_assoc, ← hq' _ (hcoord i x hx)]
  · have : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hbs h)
    rw [hb, this]; simp
end PositivityTheory.RL.Delta
