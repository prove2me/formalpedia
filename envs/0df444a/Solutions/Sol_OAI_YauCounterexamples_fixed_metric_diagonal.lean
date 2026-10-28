-- Prove2me | solution 1 for OAI.YauCounterexamples.fixed_metric_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:15:42.690012+00:00
-- url     : https://prove2.me/submissions/110cb2ad-6169-491f-b55e-6cc8f80a68ea

import Mathlib

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_FixedMetricDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
namespace YauCounterexamples
variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem fixed_metric_diagonal_oai (P W : ℕ → Set X)
    (hstep : ∀ n, ∀ x ∈ P n, ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ y ∈ P (n+1), y ∈ U ∧ ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ V ⊆ W n)
    (x₀ : X) (hx₀ : x₀ ∈ P 0) {O : Set X} (hO : IsOpen O) (hxO : x₀ ∈ O) :
    ∃ x ∈ O, ∀ n, x ∈ W n := by
  let e : ℕ → ℝ := fun n => (1/2:ℝ)^n
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have small (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) (n : ℕ) :
      ∃ r : ℝ, 0 < r ∧ r ≤ e n ∧ closedBall x r ⊆ U := by
    obtain ⟨δ,hδ,hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
    refine ⟨min (δ/2) (e n), lt_min (by linarith) (he n), min_le_right _ _, ?_⟩
    apply Subset.trans ?_ hB
    exact closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  let S (n : ℕ) := {p : X × ℝ // 0 < p.2 ∧ p.2 ≤ e n ∧ p.1 ∈ P n}
  have next (n : ℕ) (s : S n) :
      ∃ t : S (n+1), closedBall t.val.1 t.val.2 ⊆ ball s.val.1 s.val.2 ∩ W n := by
    obtain ⟨y,hyP,hyB,V,hV,hyV,hVW⟩ :=
      hstep n s.val.1 s.property.2.2 (ball s.val.1 s.val.2) isOpen_ball
        (mem_ball_self s.property.1)
    obtain ⟨r,hr,her,hsmall⟩ := small y (ball s.val.1 s.val.2 ∩ V)
      (isOpen_ball.inter hV) ⟨hyB,hyV⟩ (n+1)
    refine ⟨⟨(y,r),hr,her,hyP⟩,?_⟩
    exact hsmall.trans (inter_subset_inter_right _ hVW)
  obtain ⟨r₀,hr₀,her₀,hB₀⟩ := small x₀ O hO hxO 0
  let s₀ : S 0 := ⟨(x₀,r₀),hr₀,her₀,hx₀⟩
  let s : (n : ℕ) → S n := Nat.rec s₀ (fun n s => (next n s).choose)
  let B : ℕ → Set X := fun n => closedBall (s n).val.1 (s n).val.2
  have hBsucc (n : ℕ) : B (n+1) ⊆ ball (s n).val.1 (s n).val.2 ∩ W n :=
    (next n (s n)).choose_spec
  have hBanti : Antitone B := antitone_nat_of_succ_le fun n =>
    (hBsucc n).trans (inter_subset_left.trans ball_subset_closedBall)
  have hfinite (N : ℕ) : (⋂ n ≤ N, B n).Nonempty := by
    refine ⟨(s N).val.1,mem_iInter.mpr (fun n => mem_iInter.mpr (fun hn => ?_))⟩
    exact hBanti hn (mem_closedBall_self (s N).property.1.le)
  have hlim : Tendsto (fun n => diam (B n)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul 2
    apply squeeze_zero (fun n => diam_nonneg) (fun n => ?_) hh
    exact (diam_closedBall (s n).property.1.le).trans (mul_le_mul_of_nonneg_left (s n).property.2.1 (by norm_num))
  obtain ⟨x,hx⟩ := Metric.nonempty_iInter_of_nonempty_biInter
    (fun n => isClosed_closedBall) (fun n => isBounded_closedBall) hfinite hlim
  refine ⟨x,hB₀ (mem_iInter.mp hx 0),fun n => ?_⟩
  exact (hBsucc n (mem_iInter.mp hx (n+1))).2
end YauCounterexamples

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.fixed_metric_diagonal_oai.{u_1} := @OAI.YauCounterexamples.fixed_metric_diagonal_oai.{u_1}
