-- Prove2me | solution 1 for PositivityTheory.RL.Delta.zero_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:30.571168+00:00
-- url     : https://prove2.me/submissions/ea840378-4584-4948-92da-24e13a1f2b8c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
import Theorems.Thm_PositivityTheory_RL_Delta_exists_div

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
theorem _root_.solution (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]
end PositivityTheory.RL.Delta
