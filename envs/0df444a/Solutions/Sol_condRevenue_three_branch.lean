-- Prove2me | solution 1 for condRevenue_three_branch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:13:51.535991+00:00
-- url     : https://prove2.me/submissions/9a2588cc-a9ef-4f5b-85db-5d2ce70507a5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_update_of_gt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hpk : 0 ≤ p k) (y s : ℝ) (hy : 0 ≤ y)
    (hIs : Integrable (fun ω => revenue f p (fun i => X i ω) k s) P)
    (hIa : Integrable (fun ω => revenue f p (fun i => X i ω) k (p k)) P)
    (hIr : 0 ≤ s - y →
      Integrable (fun ω => revenue f p (fun i => X i ω) k (s - y)) P) :
    condRevenue P X f p (k + 1) y s =
      if s < p k then expRevenue P X f p k s
      else if s < p k + y then (s - p k) * f (k + 1) +
        expRevenue P X f p k (p k)
      else y * f (k + 1) + expRevenue P X f p k (s - y) := by
  have hrec : ∀ ω,
      revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
        if s < p k then revenue f p (fun i => X i ω) k s
        else if s < p k + y then
          (s - p k) * f (k + 1) + revenue f p (fun i => X i ω) k (p k)
        else y * f (k + 1) + revenue f p (fun i => X i ω) k (s - y) := by
    intro ω
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨m, rfl⟩
    have hleft := revenue_update_of_gt f p (fun i => X i ω)
      (m + 1) (m + 2) (by omega) y s
    have hmid := revenue_update_of_gt f p (fun i => X i ω)
      (m + 1) (m + 2) (by omega) y (p (m + 1))
    have hright := revenue_update_of_gt f p (fun i => X i ω)
      (m + 1) (m + 2) (by omega) y (s - y)
    simpa [revenue, Function.update_self, hleft, hmid, hright]
  unfold condRevenue
  rw [integral_congr_ae (Filter.Eventually.of_forall hrec)]
  by_cases hs : s < p k
  · simp [hs, expRevenue]
  · by_cases hsy : s < p k + y
    · simp only [if_neg hs, if_pos hsy]
      have hIc : Integrable (fun _ : Ω => (s - p k) * f (k + 1)) P :=
        integrable_const _
      rw [integral_add hIc hIa]
      simp [expRevenue]
    · simp only [if_neg hs, if_neg hsy]
      have hsy0 : 0 ≤ s - y := by
        have hle : p k + y ≤ s := le_of_not_gt hsy
        linarith
      have hIc : Integrable (fun _ : Ω => y * f (k + 1)) P := integrable_const _
      rw [integral_add hIc (hIr hsy0)]
      simp [expRevenue]
