-- Prove2me | solution 1 for RealTimeIter.Contract.mem_projTo_ball_of_dist
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:28:46.344724+00:00
-- url     : https://prove2.me/submissions/ee5e7506-4529-49eb-8c5f-5db9535c1f6a

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

set_option autoImplicit false
open RealTimeIter.Contract

theorem qqf_pull_apply {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : ι' → Option ι)
    (y : EuclideanSpace ℝ ι) (j : ι') :
    pull g y j = match g j with | some i => y i | none => 0 := rfl

theorem qqf_projTo_liftFrom (P : OCP) (k : ℕ) (w : PD P k) : projTo P k (liftFrom P k w) = w := by
  ext c
  have h := c.2
  simp [projTo, liftFrom, qqf_pull_apply, h]

theorem qqf_liftFrom_succ (P : OCP) (k : ℕ) (w : PD P (k + 1)) :
    liftFrom P (k + 1) w = liftFrom P k (projT P k w) := by
  ext c
  by_cases h : k + 1 ≤ stage c.1
  · have h' : k ≤ stage c.1 := by omega
    simp [liftFrom, projT, qqf_pull_apply, h, h']
  · by_cases h' : k ≤ stage c.1
    · have h2 : ¬ k < stage c.1 := by omega
      simp [liftFrom, projT, qqf_pull_apply, h, h', h2]
    · have h2 : ¬ k < stage c.1 := by omega
      simp [liftFrom, projT, qqf_pull_apply, h, h', h2]

theorem qqf_nrm_liftFrom (P : OCP) (ν : CompatNorms P) (k : ℕ) :
    ∀ w : PD P k, ν.nrm 0 (liftFrom P k w) = ν.nrm k w := by
  induction k with
  | zero =>
    intro w
    have : liftFrom P 0 w = w := by
      ext c
      simp [liftFrom, qqf_pull_apply]
    rw [this]
  | succ k ih =>
    intro w
    rw [qqf_liftFrom_succ, ih, ν.projT_eq]

theorem solution (P : OCP) (ν : CompatNorms P) (y0 : PD P 0) (k : ℕ)
    (z : PD P k) (r : ℝ) (hz : ν.nrm k (z - projTo P k y0) ≤ r) :
    z ∈ projTo P k '' {y | ν.nrm 0 (y - y0) ≤ r} := by
  refine ⟨y0 + liftFrom P k (z - projTo P k y0), ?_, ?_⟩
  · show ν.nrm 0 (y0 + liftFrom P k (z - projTo P k y0) - y0) ≤ r
    rw [add_sub_cancel_left, qqf_nrm_liftFrom]; exact hz
  · rw [map_add, qqf_projTo_liftFrom]; abel
