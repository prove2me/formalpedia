-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.infinite_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:23.333792+00:00
-- url     : https://prove2.me/submissions/21952de1-d718-4263-8c49-9b060d4942b5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by
  have hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I) := by
    intro a b hab
    have hre := congrArg Complex.re hab
    simp only at hre
    have e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
      intro x
      rw [show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
    rw [e1, e1] at hre
    have ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (a + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        linarith [Real.pi_gt_three]
    have hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (b + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        linarith [Real.pi_gt_three]
    have := Real.injOn_cos ha hb hre
    have h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩
end PositivityTheory.Rg.Sw.LVs.TC
