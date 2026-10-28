-- Prove2me | solution 1 for ProxLoj.Conv.prop_2_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:08:31.524627+00:00
-- url     : https://prove2.me/submissions/7e8ada31-d960-4109-b58e-ef10213801bf

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

open ProxLoj.Conv in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hH1 : H1 f) (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x) :
    Antitone (fun k => f (x k)) ∧ Summable (fun k => ‖x (k + 1) - x k‖ ^ 2) := by
  obtain ⟨hbot, u0, hu0⟩ := hproper
  obtain ⟨m, hm⟩ := hH1
  obtain ⟨hlm, hlmp, hlam⟩ := hstep
  have hlpos : ∀ k, 0 < lam k := fun k => lt_trans hlm (hlam k).1
  have hstep1 : ∀ k, f (x (k + 1)) + ((‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) : ℝ) : EReal) ≤
      f (x k) := by
    intro k
    have := hx k (x k)
    rwa [sub_self, norm_zero, show ((0 : ℝ) ^ 2 / (2 * lam k)) = 0 by ring, EReal.coe_zero,
      add_zero] at this
  have hanti : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    have h0 : (0 : EReal) ≤ ((‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) : ℝ) : EReal) := by
      have := hlpos k
      exact_mod_cast div_nonneg (sq_nonneg _) (by positivity)
    exact le_trans (le_add_of_nonneg_right h0) (hstep1 k)
  refine ⟨hanti, ?_⟩
  -- finiteness from k = 1 on
  have htop1 : f (x 1) ≠ ⊤ := by
    intro h
    have := hx 0 u0
    rw [h, EReal.top_add_coe] at this
    have h2 := top_le_iff.mp this
    rw [← EReal.coe_toReal hu0 (hbot u0), ← EReal.coe_add] at h2
    exact EReal.coe_ne_top _ h2
  have htop : ∀ k, f (x (k + 1)) ≠ ⊤ := by
    intro k htk
    have := hanti (show 1 ≤ k + 1 by omega)
    dsimp only at this
    rw [htk] at this
    exact htop1 (top_le_iff.mp this)
  set r : ℕ → ℝ := fun k => (f (x (k + 1))).toReal with hr
  have hcoe : ∀ k, f (x (k + 1)) = (r k : EReal) := fun k =>
    (EReal.coe_toReal (htop k) (hbot _)).symm
  have hrstep : ∀ k, r (k + 1) + ‖x (k + 2) - x (k + 1)‖ ^ 2 / (2 * lam (k + 1)) ≤ r k := by
    intro k
    have := hstep1 (k + 1)
    rw [hcoe (k + 1), hcoe k, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have hrm : ∀ k, m ≤ r k := by
    intro k
    have := hm (x (k + 1))
    rw [hcoe k, EReal.coe_le_coe_iff] at this
    exact this
  -- telescoping
  have htel : ∀ N, ∑ k ∈ Finset.range N, ‖x (k + 2) - x (k + 1)‖ ^ 2 / (2 * lam (k + 1)) ≤
      r 0 - r N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hrstep N
      linarith
  have hbound : ∀ N, ∑ k ∈ Finset.range N, ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 ≤
      2 * lamPlus * (r 0 - m) := by
    intro N
    have h1 : ∀ k ∈ Finset.range N, ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 ≤
        2 * lamPlus * (‖x (k + 2) - x (k + 1)‖ ^ 2 / (2 * lam (k + 1))) := by
      intro k _
      have hl := hlpos (k + 1)
      have hlu := (hlam (k + 1)).2
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have := sq_nonneg ‖x (k + 2) - x (k + 1)‖
      nlinarith
    calc ∑ k ∈ Finset.range N, ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2
        ≤ ∑ k ∈ Finset.range N,
            2 * lamPlus * (‖x (k + 2) - x (k + 1)‖ ^ 2 / (2 * lam (k + 1))) :=
          Finset.sum_le_sum h1
      _ = 2 * lamPlus * ∑ k ∈ Finset.range N, ‖x (k + 2) - x (k + 1)‖ ^ 2 / (2 * lam (k + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * lamPlus * (r 0 - m) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have := htel N; have := hrm N; linarith
  have hs : Summable (fun k => ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2) :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hbound
  exact (summable_nat_add_iff 1).mp hs
