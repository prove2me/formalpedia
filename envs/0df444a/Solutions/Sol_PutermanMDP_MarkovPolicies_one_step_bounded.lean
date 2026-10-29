-- Prove2me | solution 1 for PutermanMDP.MarkovPolicies.one_step_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:22:36.361998+00:00
-- url     : https://prove2.me/submissions/67b5e308-6814-4c83-8311-030c5825d873

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_RewardCriteria

open PutermanMDP.MarkovPolicies

theorem pmf_hasSum_toReal_one {X : Type*} (p : PMF X) : HasSum (fun x => (p x).toReal) 1 := by
  have h := ENNReal.hasSum_toReal (f := fun x => p x) (PMF.tsum_coe_ne_top p)
  rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top p a), PMF.tsum_coe] at h
  simpa using h

theorem pmf_abs_tsum_le {X : Type*} (p : PMF X) (f : X → ℝ) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    |∑' x, (p x).toReal * f x| ≤ B := by
  have hg : HasSum (fun x => (p x).toReal * B) B := by
    simpa using (pmf_hasSum_toReal_one p).mul_right B
  have := tsum_of_norm_bounded (f := fun x => (p x).toReal * f x) hg (by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hB x) ENNReal.toReal_nonneg)
  simpa [Real.norm_eq_abs] using this

theorem solution {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) (hM : RewardBounded M) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (u : S → ℝ) (hu : BoundedValue u)
    (d : (s : S) → PMF {a : A // a ∈ M.actions s}) :
    BoundedValue (oneStep M d β u) := by
  obtain ⟨Cr, hCr0, hCr⟩ := hM
  obtain ⟨Cu, hCu0, hCu⟩ := hu
  refine ⟨Cr + β * Cu, by positivity, ?_⟩
  intro s
  unfold oneStep
  apply pmf_abs_tsum_le
  intro a
  have h1 := hCr s a.val a.property
  have h2 : |∑' j : S, (M.transition s a j).toReal * u j| ≤ Cu :=
    pmf_abs_tsum_le _ _ _ hCu
  calc |M.reward s a.val + β * ∑' j : S, (M.transition s a j).toReal * u j|
      ≤ |M.reward s a.val| + |β * ∑' j : S, (M.transition s a j).toReal * u j| := abs_add_le _ _
    _ ≤ Cr + β * Cu := by
        rw [abs_mul, abs_of_nonneg hβ0]
        have := mul_le_mul_of_nonneg_left h2 hβ0
        linarith
