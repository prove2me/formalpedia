-- Prove2me | solution 1 for WaitTimePricing.Existence.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:27:02.668996+00:00
-- url     : https://prove2.me/submissions/5cd0504b-d5d4-4cbf-a856-af01680d32e9

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Theorems.Thm_WaitTimePricing_Existence_proposition_5
import Theorems.Thm_WaitTimePricing_Existence_proposition_6
import Theorems.Thm_WaitTimePricing_Existence_proposition_7
import Theorems.Thm_WaitTimePricing_Existence_proposition_8

open Set Filter WaitTimePricing.Existence

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    Tendsto (fun j : ℕ => gN M obj (2 ^ j)) atTop (nhds (gbar M obj)) ∧
    (∀ w : ℝ, 0 ≤ w →
      Tendsto (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) atTop (nhds (Vbar M obj w))) ∧
    SolvesDDE M obj (gbar M obj) (Vbar M obj) ∧
    AntitoneOn (Vbar M obj) (Icc 0 (wbar M + M.C)) ∧
    ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (Vbar M obj) := by
  have hw0 : 0 ≤ wbar M := Real.sSup_nonneg (fun x hx => le_of_lt hx.1)
  -- the loop of Algorithm 1 never modifies `V` on `[w̄, ∞)`
  have hstep : ∀ (g : ℝ) (N k : ℕ) (w : ℝ), wbar M ≤ w →
      VStep M obj g N k w = -(w - wbar M) * g := by
    intro g N k w hw
    induction k with
    | zero => rfl
    | succ k ih =>
      have hg : grid M N (N - k) ≤ wbar M := by
        unfold grid
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h; simp [hw0]
        · have hN : (0:ℝ) < N := by exact_mod_cast h
          have h1 : ((N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N k
          calc ((N - k : ℕ) : ℝ) * (wbar M / N) ≤ N * (wbar M / N) :=
                mul_le_mul_of_nonneg_right h1 (div_nonneg hw0 hN.le)
            _ = wbar M := by field_simp
      show (if grid M N (N - (k + 1)) ≤ w ∧ w < grid M N (N - k) then _ else _) = _
      rw [if_neg (fun h => absurd (lt_of_lt_of_le h.2 hg) (not_lt.mpr hw)), ih]
  have hV : ∀ w, wbar M ≤ w → Vbar M obj w = -(w - wbar M) * gbar M obj := by
    intro w hw
    have : (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) = fun _ => -(w - wbar M) * gbar M obj := by
      funext j; exact hstep _ _ _ _ hw
    unfold Vbar; rw [this]; exact (tendsto_const_nhds).limUnder_eq
  obtain ⟨-, -, -, h5⟩ := proposition_5 M hM obj
  obtain ⟨h6a, -, h6c, h6d, -⟩ := proposition_6 M hM obj
  have h7 := proposition_7 M hM obj
  obtain ⟨h8, -⟩ := proposition_8 M hM obj
  refine ⟨h5, ?_, ⟨h8, h7, ?_, ?_⟩, h6d, h6c⟩
  · intro w hw
    by_cases hwC : w ≤ wbar M + M.C
    · exact h6a w ⟨hw, hwC⟩
    · have hw' : wbar M ≤ w := by linarith [hM.C_pos]
      have : (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) = fun _ => -(w - wbar M) * gbar M obj := by
        funext j; exact hstep _ _ _ _ hw'
      rw [this, hV w hw']; exact tendsto_const_nhds
  · intro w hw
    have hd : HasDerivAt (fun x => -(x - wbar M) * gbar M obj) (-gbar M obj) w := by
      have := (((hasDerivAt_id w).sub_const (wbar M)).neg).mul_const (gbar M obj)
      simpa using this
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hw] with x hx
    exact hV x (le_of_lt hx)
  · rw [hV _ le_rfl]; ring
