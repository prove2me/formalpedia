-- Prove2me | solution 1 for SymmetricRendezvousLine.asymmetric_rendezvous_value_eq_thirteen_quarters
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T17:01:30.999434+00:00
-- url     : https://prove2.me/submissions/3363956d-c521-48be-a81f-d462e85cfc83

import Mathlib
import Definitions.Def_SymmetricRendezvousLine_defs

/-!
# Alpern–Gal asymmetric rendezvous on the line: the value is `13 / 4`

* Part U (`upper_bound`): explicit deterministic strategies achieving expected meeting
  time `13/4`, hence `asymmetricRendezvousValue ≤ 13 / 4`.
* Part L1 (`sum_meeting_ge`): for any two feasible paths, the four meeting times over the
  orientation pairs sum to at least `13`.
* Part L2 (`measurable_meetingTime`): the meeting time is measurable on the product space.
* Part L3 (`lower_bound`): integrating L1 gives `13 / 4 ≤ asymmetricRendezvousValue`.
-/

set_option autoImplicit false

open MeasureTheory

namespace SymmetricRendezvousLine.AG

open SymmetricRendezvousLine

/-! ## Common helpers -/

theorem rdvA_orient_true : orient true = 1 := by simp [orient]

theorem rdvA_orient_false : orient false = -1 := by simp [orient]

/-- If `τ ≥ 0` is a meeting time and no earlier nonnegative time is, then the meeting time
is exactly `τ`. -/
theorem meetingTime_eq_ofReal_of_first (x y : ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hm : x τ = y τ)
    (hlt : ∀ t, 0 ≤ t → t < τ → x t ≠ y t) : meetingTime x y = ENNReal.ofReal τ := by
  apply le_antisymm
  · exact iInf₂_le τ ⟨hτ, hm⟩
  · refine le_iInf₂ fun t ht => ENNReal.ofReal_le_ofReal ?_
    by_contra h
    exact hlt t ht.1 (lt_of_not_ge h) ht.2

/-! ## Part U: the upper bound -/

/-- Player I's path: forward to `2`, then back. -/
noncomputable def ubPathF (t : ℝ) : ℝ := 2 - |t - 2|

/-- Player II's path: `0 → 1 → 0 → 2 → 0` on `[0, 6]`. -/
noncomputable def ubPathG (t : ℝ) : ℝ := max (1 - |t - 1|) (2 - |t - 4|)

theorem tent_lipschitz (k m s t : ℝ) : |(k - |s - m|) - (k - |t - m|)| ≤ |s - t| := by
  have h1 := abs_sub_abs_le_abs_sub (s - m) (t - m)
  have h2 := abs_sub_abs_le_abs_sub (t - m) (s - m)
  have e1 : s - m - (t - m) = s - t := by ring
  have e2 : t - m - (s - m) = -(s - t) := by ring
  rw [e1] at h1
  rw [e2, abs_neg] at h2
  rw [abs_le]; constructor <;> linarith

theorem ubPathF_feasible : IsFeasiblePath ubPathF :=
  ⟨by norm_num [ubPathF], fun s t _ _ => tent_lipschitz 2 2 s t⟩

theorem ubPathG_feasible : IsFeasiblePath ubPathG := by
  refine ⟨by norm_num [ubPathG], fun s t _ _ => ?_⟩
  unfold ubPathG
  exact (abs_max_sub_max_le_max (1 - |s - 1|) (2 - |s - 4|) (1 - |t - 1|) (2 - |t - 4|)).trans
    (max_le (tent_lipschitz 1 1 s t) (tent_lipschitz 2 4 s t))

theorem ub_T_tt :
    meetingTime (fun t => orient true * ubPathF t) (fun t => 2 + orient true * ubPathG t)
      = ENNReal.ofReal 2 := by
  apply meetingTime_eq_ofReal_of_first _ _ 2 (by norm_num)
  · norm_num [rdvA_orient_true, ubPathF, ubPathG]
  · intro t h0 hlt
    simp only [rdvA_orient_true, one_mul, ubPathF, ubPathG]
    have hf : 2 - |t - 2| = t := by rw [abs_of_neg (by linarith)]; ring
    have hg : 0 ≤ max (1 - |t - 1|) (2 - |t - 4|) :=
      le_max_of_le_left (by
        have := abs_le.mpr (⟨by linarith, by linarith⟩ : -1 ≤ t - 1 ∧ t - 1 ≤ 1); linarith)
    intro h; rw [hf] at h; linarith

theorem ub_T_tf :
    meetingTime (fun t => orient true * ubPathF t) (fun t => 2 + orient false * ubPathG t)
      = ENNReal.ofReal 1 := by
  apply meetingTime_eq_ofReal_of_first _ _ 1 (by norm_num)
  · norm_num [rdvA_orient_true, rdvA_orient_false, ubPathF, ubPathG]
  · intro t h0 hlt
    simp only [rdvA_orient_true, rdvA_orient_false, one_mul, ubPathF, ubPathG]
    have hf : 2 - |t - 2| = t := by rw [abs_of_neg (by linarith)]; ring
    have hg : max (1 - |t - 1|) (2 - |t - 4|) = t := by
      rw [abs_of_neg (by linarith : t - 1 < 0), abs_of_neg (by linarith : t - 4 < 0)]
      rw [max_eq_left (by linarith)]; ring
    rw [hf, hg]; intro h; linarith

theorem ub_T_ft :
    meetingTime (fun t => orient false * ubPathF t) (fun t => 2 + orient true * ubPathG t)
      = ENNReal.ofReal 6 := by
  apply meetingTime_eq_ofReal_of_first _ _ 6 (by norm_num)
  · norm_num [rdvA_orient_true, rdvA_orient_false, ubPathF, ubPathG]
  · intro t h0 hlt
    simp only [rdvA_orient_true, rdvA_orient_false, one_mul, ubPathF, ubPathG]
    have hf : -2 < 2 - |t - 2| := by
      have := abs_lt.mpr (⟨by linarith, by linarith⟩ : -4 < t - 2 ∧ t - 2 < 4); linarith
    have hg : 0 ≤ max (1 - |t - 1|) (2 - |t - 4|) := by
      rcases le_total t 2 with h2 | h2
      · exact le_max_of_le_left
          (by have := abs_le.mpr (⟨by linarith, by linarith⟩ : -1 ≤ t - 1 ∧ t - 1 ≤ 1); linarith)
      · exact le_max_of_le_right
          (by have := abs_le.mpr (⟨by linarith, by linarith⟩ : -2 ≤ t - 4 ∧ t - 4 ≤ 2); linarith)
    intro h; linarith

theorem ub_T_ff :
    meetingTime (fun t => orient false * ubPathF t) (fun t => 2 + orient false * ubPathG t)
      = ENNReal.ofReal 4 := by
  apply meetingTime_eq_ofReal_of_first _ _ 4 (by norm_num)
  · norm_num [rdvA_orient_true, rdvA_orient_false, ubPathF, ubPathG]
  · intro t h0 hlt
    simp only [rdvA_orient_false, ubPathF, ubPathG]
    rcases le_total t 2 with h2 | h2
    · have hf : 2 - |t - 2| = t := by rw [abs_of_nonpos (by linarith)]; ring
      have hg : max (1 - |t - 1|) (2 - |t - 4|) ≤ t := by
        refine max_le ?_ ?_
        · have := le_abs_self (t - 1); have := neg_abs_le (t - 1); linarith
        · have := le_abs_self (t - 4); have := neg_abs_le (t - 4); linarith
      rw [hf]; intro h; linarith
    · have hf : 2 - |t - 2| = 4 - t := by rw [abs_of_nonneg (by linarith)]; ring
      have hg : max (1 - |t - 1|) (2 - |t - 4|) = t - 2 := by
        rw [abs_of_nonneg (by linarith : 0 ≤ t - 1), abs_of_neg (by linarith : t - 4 < 0)]
        rw [max_eq_right (by linarith)]; ring
      rw [hf, hg]; intro h; linarith

/-- Player I's (deterministic) strategy. -/
noncomputable def ubStratF : MixedStrategy where
  Ω := Unit
  P := Measure.dirac ()
  path := fun _ => ubPathF
  path_feasible := fun _ => ubPathF_feasible
  path_measurable := fun _ => measurable_const

/-- Player II's (deterministic) strategy. -/
noncomputable def ubStratG : MixedStrategy where
  Ω := Unit
  P := Measure.dirac ()
  path := fun _ => ubPathG
  path_feasible := fun _ => ubPathG_feasible
  path_measurable := fun _ => measurable_const

theorem expectedMeetingTime_ubStrat : expectedMeetingTime ubStratF ubStratG = 13 / 4 := by
  unfold expectedMeetingTime
  have hF : ∀ ω, ubStratF.path ω = ubPathF := fun _ => rfl
  have hG : ∀ ω, ubStratG.path ω = ubPathG := fun _ => rfl
  simp only [hF, hG, lintegral_const, measure_univ, mul_one, Fintype.sum_bool]
  rw [ub_T_tt, ub_T_tf, ub_T_ft, ub_T_ff]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [show (2 : ENNReal) + 1 + (6 + 4) = 13 by norm_num, one_div, ENNReal.div_eq_inv_mul]

/-- **Part U.** The asymmetric rendezvous value is at most `13/4`. -/
theorem upper_bound : asymmetricRendezvousValue ≤ 13 / 4 := by
  rw [← expectedMeetingTime_ubStrat]
  exact iInf₂_le (f := fun S₁ S₂ : MixedStrategy => expectedMeetingTime S₁ S₂) ubStratF ubStratG

/-! ## Part L1: the core deterministic inequality -/

theorem rdvA_pair_lo {x y s t : ℝ} (h : |x - y| ≤ |s - t|) (hst : s ≤ t) : |x - y| ≤ t - s := by
  rwa [abs_sub_comm s t, abs_of_nonneg (show (0:ℝ) ≤ t - s by linarith)] at h

theorem rdvA_pair_hi {x y s t : ℝ} (h : |x - y| ≤ |s - t|) (hst : t ≤ s) : |x - y| ≤ s - t := by
  rwa [abs_of_nonneg (show (0:ℝ) ≤ s - t by linarith)] at h

/-- The real inequality behind the Alpern–Gal lower bound: four meeting times, one per
orientation pair, of two `1`-Lipschitz paths started at the origin sum to at least `13`.
Proof: sort the four times (a decision tree with 24 leaves); in each ordering the bound is a
linear consequence of the meeting conditions, the bounds `|aᵢ|, |cᵢ| ≤ tᵢ`, and the Lipschitz
bounds between consecutive times. -/
theorem rdvA_key_real (t₀ t₁ t₂ t₃ a₀ a₁ a₂ a₃ c₀ c₁ c₂ c₃ : ℝ)
    (m₀ : a₀ = 2 + c₀) (m₁ : a₁ = 2 - c₁) (m₂ : -a₂ = 2 + c₂) (m₃ : -a₃ = 2 - c₃)
    (A₀ : |a₀| ≤ t₀) (A₁ : |a₁| ≤ t₁) (A₂ : |a₂| ≤ t₂) (A₃ : |a₃| ≤ t₃)
    (C₀ : |c₀| ≤ t₀) (C₁ : |c₁| ≤ t₁) (C₂ : |c₂| ≤ t₂) (C₃ : |c₃| ≤ t₃)
    (A₀₁ : |a₀ - a₁| ≤ |t₀ - t₁|) (A₀₂ : |a₀ - a₂| ≤ |t₀ - t₂|) (A₀₃ : |a₀ - a₃| ≤ |t₀ - t₃|)
    (A₁₂ : |a₁ - a₂| ≤ |t₁ - t₂|) (A₁₃ : |a₁ - a₃| ≤ |t₁ - t₃|) (A₂₃ : |a₂ - a₃| ≤ |t₂ - t₃|)
    (C₀₁ : |c₀ - c₁| ≤ |t₀ - t₁|) (C₀₂ : |c₀ - c₂| ≤ |t₀ - t₂|) (C₀₃ : |c₀ - c₃| ≤ |t₀ - t₃|)
    (C₁₂ : |c₁ - c₂| ≤ |t₁ - t₂|) (C₁₃ : |c₁ - c₃| ≤ |t₁ - t₃|) (C₂₃ : |c₂ - c₃| ≤ |t₂ - t₃|) :
    13 ≤ t₀ + t₁ + t₂ + t₃ := by
  obtain ⟨A₀a, A₀b⟩ := abs_le.mp A₀
  obtain ⟨A₁a, A₁b⟩ := abs_le.mp A₁
  obtain ⟨A₂a, A₂b⟩ := abs_le.mp A₂
  obtain ⟨A₃a, A₃b⟩ := abs_le.mp A₃
  obtain ⟨C₀a, C₀b⟩ := abs_le.mp C₀
  obtain ⟨C₁a, C₁b⟩ := abs_le.mp C₁
  obtain ⟨C₂a, C₂b⟩ := abs_le.mp C₂
  obtain ⟨C₃a, C₃b⟩ := abs_le.mp C₃
  rcases le_total t₁ t₀ with q1a | q1b
  · rcases le_total t₂ t₀ with q2a | q2b
    · rcases le_total t₂ t₁ with q3a | q3b
      · rcases le_total t₃ t₁ with q4a | q4b
        · rcases le_total t₃ t₂ with q5a | q5b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q5a, (abs_le.mp (rdvA_pair_hi A₂₃ q5a)).1,
              (abs_le.mp (rdvA_pair_hi A₂₃ q5a)).2, (abs_le.mp (rdvA_pair_hi C₂₃ q5a)).1,
              (abs_le.mp (rdvA_pair_hi C₂₃ q5a)).2, q3a, (abs_le.mp (rdvA_pair_hi A₁₂ q3a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₂ q3a)).2, (abs_le.mp (rdvA_pair_hi C₁₂ q3a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₂ q3a)).2, q1a, (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).2, (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q5b, (abs_le.mp (rdvA_pair_lo A₂₃ q5b)).1,
              (abs_le.mp (rdvA_pair_lo A₂₃ q5b)).2, (abs_le.mp (rdvA_pair_lo C₂₃ q5b)).1,
              (abs_le.mp (rdvA_pair_lo C₂₃ q5b)).2, q4a, (abs_le.mp (rdvA_pair_hi A₁₃ q4a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₃ q4a)).2, (abs_le.mp (rdvA_pair_hi C₁₃ q4a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₃ q4a)).2, q1a, (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).2, (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).2]
        · rcases le_total t₃ t₀ with q6a | q6b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q3a, (abs_le.mp (rdvA_pair_hi A₁₂ q3a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₂ q3a)).2, (abs_le.mp (rdvA_pair_hi C₁₂ q3a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₂ q3a)).2, q4b, (abs_le.mp (rdvA_pair_lo A₁₃ q4b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₃ q4b)).2, (abs_le.mp (rdvA_pair_lo C₁₃ q4b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₃ q4b)).2, q6a, (abs_le.mp (rdvA_pair_hi A₀₃ q6a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₃ q6a)).2, (abs_le.mp (rdvA_pair_hi C₀₃ q6a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₃ q6a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q3a, (abs_le.mp (rdvA_pair_hi A₁₂ q3a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₂ q3a)).2, (abs_le.mp (rdvA_pair_hi C₁₂ q3a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₂ q3a)).2, q1a, (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).2, (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).2, q6b, (abs_le.mp (rdvA_pair_lo A₀₃ q6b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₃ q6b)).2, (abs_le.mp (rdvA_pair_lo C₀₃ q6b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₃ q6b)).2]
      · rcases le_total t₃ t₂ with q7a | q7b
        · rcases le_total t₃ t₁ with q8a | q8b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q8a, (abs_le.mp (rdvA_pair_hi A₁₃ q8a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₃ q8a)).2, (abs_le.mp (rdvA_pair_hi C₁₃ q8a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₃ q8a)).2, q3b, (abs_le.mp (rdvA_pair_lo A₁₂ q3b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₂ q3b)).2, (abs_le.mp (rdvA_pair_lo C₁₂ q3b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₂ q3b)).2, q2a, (abs_le.mp (rdvA_pair_hi A₀₂ q2a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₂ q2a)).2, (abs_le.mp (rdvA_pair_hi C₀₂ q2a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₂ q2a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q8b, (abs_le.mp (rdvA_pair_lo A₁₃ q8b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₃ q8b)).2, (abs_le.mp (rdvA_pair_lo C₁₃ q8b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₃ q8b)).2, q7a, (abs_le.mp (rdvA_pair_hi A₂₃ q7a)).1,
              (abs_le.mp (rdvA_pair_hi A₂₃ q7a)).2, (abs_le.mp (rdvA_pair_hi C₂₃ q7a)).1,
              (abs_le.mp (rdvA_pair_hi C₂₃ q7a)).2, q2a, (abs_le.mp (rdvA_pair_hi A₀₂ q2a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₂ q2a)).2, (abs_le.mp (rdvA_pair_hi C₀₂ q2a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₂ q2a)).2]
        · rcases le_total t₃ t₀ with q9a | q9b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q3b, (abs_le.mp (rdvA_pair_lo A₁₂ q3b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₂ q3b)).2, (abs_le.mp (rdvA_pair_lo C₁₂ q3b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₂ q3b)).2, q7b, (abs_le.mp (rdvA_pair_lo A₂₃ q7b)).1,
              (abs_le.mp (rdvA_pair_lo A₂₃ q7b)).2, (abs_le.mp (rdvA_pair_lo C₂₃ q7b)).1,
              (abs_le.mp (rdvA_pair_lo C₂₃ q7b)).2, q9a, (abs_le.mp (rdvA_pair_hi A₀₃ q9a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₃ q9a)).2, (abs_le.mp (rdvA_pair_hi C₀₃ q9a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₃ q9a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q3b, (abs_le.mp (rdvA_pair_lo A₁₂ q3b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₂ q3b)).2, (abs_le.mp (rdvA_pair_lo C₁₂ q3b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₂ q3b)).2, q2a, (abs_le.mp (rdvA_pair_hi A₀₂ q2a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₂ q2a)).2, (abs_le.mp (rdvA_pair_hi C₀₂ q2a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₂ q2a)).2, q9b, (abs_le.mp (rdvA_pair_lo A₀₃ q9b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₃ q9b)).2, (abs_le.mp (rdvA_pair_lo C₀₃ q9b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₃ q9b)).2]
    · rcases le_total t₃ t₀ with q10a | q10b
      · rcases le_total t₃ t₁ with q11a | q11b
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q11a, (abs_le.mp (rdvA_pair_hi A₁₃ q11a)).1,
            (abs_le.mp (rdvA_pair_hi A₁₃ q11a)).2, (abs_le.mp (rdvA_pair_hi C₁₃ q11a)).1,
            (abs_le.mp (rdvA_pair_hi C₁₃ q11a)).2, q1a, (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).1,
            (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).2, (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).1,
            (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).2, q2b, (abs_le.mp (rdvA_pair_lo A₀₂ q2b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₂ q2b)).2, (abs_le.mp (rdvA_pair_lo C₀₂ q2b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₂ q2b)).2]
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q11b, (abs_le.mp (rdvA_pair_lo A₁₃ q11b)).1,
            (abs_le.mp (rdvA_pair_lo A₁₃ q11b)).2, (abs_le.mp (rdvA_pair_lo C₁₃ q11b)).1,
            (abs_le.mp (rdvA_pair_lo C₁₃ q11b)).2, q10a, (abs_le.mp (rdvA_pair_hi A₀₃ q10a)).1,
            (abs_le.mp (rdvA_pair_hi A₀₃ q10a)).2, (abs_le.mp (rdvA_pair_hi C₀₃ q10a)).1,
            (abs_le.mp (rdvA_pair_hi C₀₃ q10a)).2, q2b, (abs_le.mp (rdvA_pair_lo A₀₂ q2b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₂ q2b)).2, (abs_le.mp (rdvA_pair_lo C₀₂ q2b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₂ q2b)).2]
      · rcases le_total t₃ t₂ with q12a | q12b
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q1a, (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).1,
            (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).2, (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).1,
            (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).2, q10b, (abs_le.mp (rdvA_pair_lo A₀₃ q10b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₃ q10b)).2, (abs_le.mp (rdvA_pair_lo C₀₃ q10b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₃ q10b)).2, q12a, (abs_le.mp (rdvA_pair_hi A₂₃ q12a)).1,
            (abs_le.mp (rdvA_pair_hi A₂₃ q12a)).2, (abs_le.mp (rdvA_pair_hi C₂₃ q12a)).1,
            (abs_le.mp (rdvA_pair_hi C₂₃ q12a)).2]
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q1a, (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).1,
            (abs_le.mp (rdvA_pair_hi A₀₁ q1a)).2, (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).1,
            (abs_le.mp (rdvA_pair_hi C₀₁ q1a)).2, q2b, (abs_le.mp (rdvA_pair_lo A₀₂ q2b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₂ q2b)).2, (abs_le.mp (rdvA_pair_lo C₀₂ q2b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₂ q2b)).2, q12b, (abs_le.mp (rdvA_pair_lo A₂₃ q12b)).1,
            (abs_le.mp (rdvA_pair_lo A₂₃ q12b)).2, (abs_le.mp (rdvA_pair_lo C₂₃ q12b)).1,
            (abs_le.mp (rdvA_pair_lo C₂₃ q12b)).2]
  · rcases le_total t₂ t₁ with q13a | q13b
    · rcases le_total t₂ t₀ with q14a | q14b
      · rcases le_total t₃ t₀ with q15a | q15b
        · rcases le_total t₃ t₂ with q16a | q16b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q16a, (abs_le.mp (rdvA_pair_hi A₂₃ q16a)).1,
              (abs_le.mp (rdvA_pair_hi A₂₃ q16a)).2, (abs_le.mp (rdvA_pair_hi C₂₃ q16a)).1,
              (abs_le.mp (rdvA_pair_hi C₂₃ q16a)).2, q14a, (abs_le.mp (rdvA_pair_hi A₀₂ q14a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₂ q14a)).2, (abs_le.mp (rdvA_pair_hi C₀₂ q14a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₂ q14a)).2, q1b, (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).2, (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q16b, (abs_le.mp (rdvA_pair_lo A₂₃ q16b)).1,
              (abs_le.mp (rdvA_pair_lo A₂₃ q16b)).2, (abs_le.mp (rdvA_pair_lo C₂₃ q16b)).1,
              (abs_le.mp (rdvA_pair_lo C₂₃ q16b)).2, q15a, (abs_le.mp (rdvA_pair_hi A₀₃ q15a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₃ q15a)).2, (abs_le.mp (rdvA_pair_hi C₀₃ q15a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₃ q15a)).2, q1b, (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).2, (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).2]
        · rcases le_total t₃ t₁ with q17a | q17b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q14a, (abs_le.mp (rdvA_pair_hi A₀₂ q14a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₂ q14a)).2, (abs_le.mp (rdvA_pair_hi C₀₂ q14a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₂ q14a)).2, q15b, (abs_le.mp (rdvA_pair_lo A₀₃ q15b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₃ q15b)).2, (abs_le.mp (rdvA_pair_lo C₀₃ q15b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₃ q15b)).2, q17a, (abs_le.mp (rdvA_pair_hi A₁₃ q17a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₃ q17a)).2, (abs_le.mp (rdvA_pair_hi C₁₃ q17a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₃ q17a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q14a, (abs_le.mp (rdvA_pair_hi A₀₂ q14a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₂ q14a)).2, (abs_le.mp (rdvA_pair_hi C₀₂ q14a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₂ q14a)).2, q1b, (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).2, (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).2, q17b, (abs_le.mp (rdvA_pair_lo A₁₃ q17b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₃ q17b)).2, (abs_le.mp (rdvA_pair_lo C₁₃ q17b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₃ q17b)).2]
      · rcases le_total t₃ t₂ with q18a | q18b
        · rcases le_total t₃ t₀ with q19a | q19b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q19a, (abs_le.mp (rdvA_pair_hi A₀₃ q19a)).1,
              (abs_le.mp (rdvA_pair_hi A₀₃ q19a)).2, (abs_le.mp (rdvA_pair_hi C₀₃ q19a)).1,
              (abs_le.mp (rdvA_pair_hi C₀₃ q19a)).2, q14b, (abs_le.mp (rdvA_pair_lo A₀₂ q14b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₂ q14b)).2, (abs_le.mp (rdvA_pair_lo C₀₂ q14b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₂ q14b)).2, q13a, (abs_le.mp (rdvA_pair_hi A₁₂ q13a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₂ q13a)).2, (abs_le.mp (rdvA_pair_hi C₁₂ q13a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₂ q13a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q19b, (abs_le.mp (rdvA_pair_lo A₀₃ q19b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₃ q19b)).2, (abs_le.mp (rdvA_pair_lo C₀₃ q19b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₃ q19b)).2, q18a, (abs_le.mp (rdvA_pair_hi A₂₃ q18a)).1,
              (abs_le.mp (rdvA_pair_hi A₂₃ q18a)).2, (abs_le.mp (rdvA_pair_hi C₂₃ q18a)).1,
              (abs_le.mp (rdvA_pair_hi C₂₃ q18a)).2, q13a, (abs_le.mp (rdvA_pair_hi A₁₂ q13a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₂ q13a)).2, (abs_le.mp (rdvA_pair_hi C₁₂ q13a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₂ q13a)).2]
        · rcases le_total t₃ t₁ with q20a | q20b
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q14b, (abs_le.mp (rdvA_pair_lo A₀₂ q14b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₂ q14b)).2, (abs_le.mp (rdvA_pair_lo C₀₂ q14b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₂ q14b)).2, q18b, (abs_le.mp (rdvA_pair_lo A₂₃ q18b)).1,
              (abs_le.mp (rdvA_pair_lo A₂₃ q18b)).2, (abs_le.mp (rdvA_pair_lo C₂₃ q18b)).1,
              (abs_le.mp (rdvA_pair_lo C₂₃ q18b)).2, q20a, (abs_le.mp (rdvA_pair_hi A₁₃ q20a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₃ q20a)).2, (abs_le.mp (rdvA_pair_hi C₁₃ q20a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₃ q20a)).2]
          · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
              C₁b, C₂a, C₂b, C₃a, C₃b, q14b, (abs_le.mp (rdvA_pair_lo A₀₂ q14b)).1,
              (abs_le.mp (rdvA_pair_lo A₀₂ q14b)).2, (abs_le.mp (rdvA_pair_lo C₀₂ q14b)).1,
              (abs_le.mp (rdvA_pair_lo C₀₂ q14b)).2, q13a, (abs_le.mp (rdvA_pair_hi A₁₂ q13a)).1,
              (abs_le.mp (rdvA_pair_hi A₁₂ q13a)).2, (abs_le.mp (rdvA_pair_hi C₁₂ q13a)).1,
              (abs_le.mp (rdvA_pair_hi C₁₂ q13a)).2, q20b, (abs_le.mp (rdvA_pair_lo A₁₃ q20b)).1,
              (abs_le.mp (rdvA_pair_lo A₁₃ q20b)).2, (abs_le.mp (rdvA_pair_lo C₁₃ q20b)).1,
              (abs_le.mp (rdvA_pair_lo C₁₃ q20b)).2]
    · rcases le_total t₃ t₁ with q21a | q21b
      · rcases le_total t₃ t₀ with q22a | q22b
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q22a, (abs_le.mp (rdvA_pair_hi A₀₃ q22a)).1,
            (abs_le.mp (rdvA_pair_hi A₀₃ q22a)).2, (abs_le.mp (rdvA_pair_hi C₀₃ q22a)).1,
            (abs_le.mp (rdvA_pair_hi C₀₃ q22a)).2, q1b, (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).2, (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).2, q13b, (abs_le.mp (rdvA_pair_lo A₁₂ q13b)).1,
            (abs_le.mp (rdvA_pair_lo A₁₂ q13b)).2, (abs_le.mp (rdvA_pair_lo C₁₂ q13b)).1,
            (abs_le.mp (rdvA_pair_lo C₁₂ q13b)).2]
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q22b, (abs_le.mp (rdvA_pair_lo A₀₃ q22b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₃ q22b)).2, (abs_le.mp (rdvA_pair_lo C₀₃ q22b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₃ q22b)).2, q21a, (abs_le.mp (rdvA_pair_hi A₁₃ q21a)).1,
            (abs_le.mp (rdvA_pair_hi A₁₃ q21a)).2, (abs_le.mp (rdvA_pair_hi C₁₃ q21a)).1,
            (abs_le.mp (rdvA_pair_hi C₁₃ q21a)).2, q13b, (abs_le.mp (rdvA_pair_lo A₁₂ q13b)).1,
            (abs_le.mp (rdvA_pair_lo A₁₂ q13b)).2, (abs_le.mp (rdvA_pair_lo C₁₂ q13b)).1,
            (abs_le.mp (rdvA_pair_lo C₁₂ q13b)).2]
      · rcases le_total t₃ t₂ with q23a | q23b
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q1b, (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).2, (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).2, q21b, (abs_le.mp (rdvA_pair_lo A₁₃ q21b)).1,
            (abs_le.mp (rdvA_pair_lo A₁₃ q21b)).2, (abs_le.mp (rdvA_pair_lo C₁₃ q21b)).1,
            (abs_le.mp (rdvA_pair_lo C₁₃ q21b)).2, q23a, (abs_le.mp (rdvA_pair_hi A₂₃ q23a)).1,
            (abs_le.mp (rdvA_pair_hi A₂₃ q23a)).2, (abs_le.mp (rdvA_pair_hi C₂₃ q23a)).1,
            (abs_le.mp (rdvA_pair_hi C₂₃ q23a)).2]
        · linarith only [m₀, m₁, m₂, m₃, A₀a, A₀b, A₁a, A₁b, A₂a, A₂b, A₃a, A₃b, C₀a, C₀b, C₁a,
            C₁b, C₂a, C₂b, C₃a, C₃b, q1b, (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).1,
            (abs_le.mp (rdvA_pair_lo A₀₁ q1b)).2, (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).1,
            (abs_le.mp (rdvA_pair_lo C₀₁ q1b)).2, q13b, (abs_le.mp (rdvA_pair_lo A₁₂ q13b)).1,
            (abs_le.mp (rdvA_pair_lo A₁₂ q13b)).2, (abs_le.mp (rdvA_pair_lo C₁₂ q13b)).1,
            (abs_le.mp (rdvA_pair_lo C₁₂ q13b)).2, q23b, (abs_le.mp (rdvA_pair_lo A₂₃ q23b)).1,
            (abs_le.mp (rdvA_pair_lo A₂₃ q23b)).2, (abs_le.mp (rdvA_pair_lo C₂₃ q23b)).1,
            (abs_le.mp (rdvA_pair_lo C₂₃ q23b)).2]

theorem rdvA_abs_le_of_feasible (f : ℝ → ℝ) (hf : IsFeasiblePath f) (t : ℝ) (ht : 0 ≤ t) :
    |f t| ≤ t := by
  have h := hf.2 t 0 ht le_rfl
  rwa [hf.1, sub_zero, sub_zero, abs_of_nonneg ht] at h

/-- **Part L1 (interface lemma).** For feasible `f, g`, the four meeting times (one per
orientation pair) sum to at least `13`. -/
theorem sum_meeting_ge (f g : ℝ → ℝ) (hf : IsFeasiblePath f) (hg : IsFeasiblePath g) :
    (13 : ENNReal) ≤ ∑ b₁ : Bool, ∑ b₂ : Bool,
      meetingTime (fun t => orient b₁ * f t) (fun t => 2 + orient b₂ * g t) := by
  simp only [Fintype.sum_bool, meetingTime, rdvA_orient_true, rdvA_orient_false]
  simp only [ENNReal.iInf_add, ENNReal.add_iInf, le_iInf_iff]
  rintro t₃ ⟨h₃, e₃⟩ t₂ ⟨h₂, e₂⟩ t₁ ⟨h₁, e₁⟩ t₀ ⟨h₀, e₀⟩
  rw [← ENNReal.ofReal_add h₀ h₁, ← ENNReal.ofReal_add h₂ h₃,
    ← ENNReal.ofReal_add (add_nonneg h₀ h₁) (add_nonneg h₂ h₃),
    show (13 : ENNReal) = ENNReal.ofReal 13 by norm_num]
  apply ENNReal.ofReal_le_ofReal
  have := rdvA_key_real t₀ t₁ t₂ t₃ (f t₀) (f t₁) (f t₂) (f t₃) (g t₀) (g t₁) (g t₂) (g t₃)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (rdvA_abs_le_of_feasible f hf t₀ h₀) (rdvA_abs_le_of_feasible f hf t₁ h₁)
    (rdvA_abs_le_of_feasible f hf t₂ h₂) (rdvA_abs_le_of_feasible f hf t₃ h₃)
    (rdvA_abs_le_of_feasible g hg t₀ h₀) (rdvA_abs_le_of_feasible g hg t₁ h₁)
    (rdvA_abs_le_of_feasible g hg t₂ h₂) (rdvA_abs_le_of_feasible g hg t₃ h₃)
    (hf.2 _ _ h₀ h₁) (hf.2 _ _ h₀ h₂) (hf.2 _ _ h₀ h₃)
    (hf.2 _ _ h₁ h₂) (hf.2 _ _ h₁ h₃) (hf.2 _ _ h₂ h₃)
    (hg.2 _ _ h₀ h₁) (hg.2 _ _ h₀ h₂) (hg.2 _ _ h₀ h₃)
    (hg.2 _ _ h₁ h₂) (hg.2 _ _ h₁ h₃) (hg.2 _ _ h₂ h₃)
  linarith


/-! ### Part L2: measurability of the meeting time -/

/-- A feasible path is continuous on `[0, ∞)`. -/
theorem continuousOn_of_feasible {f : ℝ → ℝ} (hf : IsFeasiblePath f) :
    ContinuousOn f (Set.Ici 0) := by
  have hL : LipschitzOnWith 1 f (Set.Ici 0) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      simpa [Real.dist_eq] using hf.2 x y hx hy
  exact hL.continuousOn

/-- If two trajectories meet at some time and their difference is continuous on `[0, ∞)`,
then the meeting time is attained. -/
theorem meetingTime_attained {x y : ℝ → ℝ}
    (hc : ContinuousOn (fun t => x t - y t) (Set.Ici 0))
    (hne : ∃ t, 0 ≤ t ∧ x t = y t) :
    ∃ τ, 0 ≤ τ ∧ x τ = y τ ∧ meetingTime x y = ENNReal.ofReal τ := by
  set S : Set ℝ := {t | 0 ≤ t ∧ x t = y t} with hSdef
  have hS : S = Set.Ici 0 ∩ (fun t => x t - y t) ⁻¹' {0} := by
    ext t
    simp [hSdef, sub_eq_zero]
  have hclosed : IsClosed S := by
    rw [hS]
    exact hc.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hnonempty : S.Nonempty := by
    obtain ⟨t, ht0, ht⟩ := hne
    exact ⟨t, ht0, ht⟩
  have hmem : sInf S ∈ S := hclosed.csInf_mem hnonempty hbdd
  refine ⟨sInf S, hmem.1, hmem.2, ?_⟩
  apply le_antisymm
  · exact iInf₂_le (sInf S) hmem
  · refine le_iInf₂ fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (csInf_le hbdd ht)

/-- If the trajectories never meet, the meeting time is `⊤`. -/
theorem meetingTime_eq_top_of_not {x y : ℝ → ℝ} (h : ¬ ∃ t, 0 ≤ t ∧ x t = y t) :
    meetingTime x y = ⊤ := by
  apply le_antisymm le_top
  refine le_iInf₂ fun t ht => ?_
  exact absurd ⟨t, ht.1, ht.2⟩ h

/-- Sublevel sets of the meeting time. -/
theorem meetingTime_le_ofReal_iff {x y : ℝ → ℝ}
    (hc : ContinuousOn (fun t => x t - y t) (Set.Ici 0)) {s : ℝ} (hs : 0 ≤ s) :
    meetingTime x y ≤ ENNReal.ofReal s ↔ ∃ t, 0 ≤ t ∧ t ≤ s ∧ x t - y t = 0 := by
  constructor
  · intro hle
    by_cases hne : ∃ t, 0 ≤ t ∧ x t = y t
    · obtain ⟨τ, hτ0, hτ, hEq⟩ := meetingTime_attained hc hne
      rw [hEq, ENNReal.ofReal_le_ofReal_iff hs] at hle
      exact ⟨τ, hτ0, hle, by rw [hτ, sub_self]⟩
    · rw [meetingTime_eq_top_of_not hne] at hle
      exact absurd (top_le_iff.mp hle) ENNReal.ofReal_ne_top
  · rintro ⟨t, ht0, hts, hxt⟩
    calc meetingTime x y ≤ ENNReal.ofReal t := iInf₂_le t ⟨ht0, sub_eq_zero.mp hxt⟩
      _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hts

/-- Existence of a zero on `[0, s]` of a function continuous on `[0, ∞)`, expressed through
countably many conditions at rational times. -/
theorem exists_zero_iff_rat {D : ℝ → ℝ} (hc : ContinuousOn D (Set.Ici 0)) {s : ℝ}
    (hs : 0 ≤ s) :
    (∃ t, 0 ≤ t ∧ t ≤ s ∧ D t = 0) ↔
      ∀ k : ℕ, ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s ∧ |D q| < 1 / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨t, ht0, hts, hDt⟩ k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp (hc t ht0) _ hε
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · subst h0
      refine ⟨0, by simp, by simpa using hs, ?_⟩
      simpa [hDt] using hε
    · have hlt : max 0 (t - δ) < t := max_lt hpos (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq0 : (0 : ℝ) ≤ q := le_trans (le_max_left _ _) hq1.le
      have hqδ : t - δ < q := lt_of_le_of_lt (le_max_right _ _) hq1
      refine ⟨q, hq0, by linarith, ?_⟩
      have hdist : dist (q : ℝ) t < δ := by
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith
      have := hδc (show (q : ℝ) ∈ Set.Ici 0 from hq0) hdist
      rw [Real.dist_eq, hDt, sub_zero] at this
      exact this
  · intro h
    have hcpt : IsCompact (Set.Icc (0 : ℝ) s) := isCompact_Icc
    have hne : (Set.Icc (0 : ℝ) s).Nonempty := ⟨0, le_refl 0, hs⟩
    have hcabs : ContinuousOn (fun t => |D t|) (Set.Icc 0 s) :=
      (hc.mono Set.Icc_subset_Ici_self).abs
    obtain ⟨t, ht, hmin⟩ := hcpt.exists_isMinOn hne hcabs
    refine ⟨t, ht.1, ht.2, ?_⟩
    by_contra hDt
    have hpos : 0 < |D t| := abs_pos.mpr hDt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    obtain ⟨q, hq0, hqs, hq⟩ := h k
    have := hmin (show (q : ℝ) ∈ Set.Icc 0 s from ⟨hq0, hqs⟩)
    simp only [Set.mem_ofPred_eq] at this
    linarith

/-- Generic measurability of the meeting time of a random pair of trajectories. -/
theorem measurable_meetingTime_of {α : Type*} [MeasurableSpace α] (x y : α → ℝ → ℝ)
    (hxm : ∀ t, Measurable fun a => x a t) (hym : ∀ t, Measurable fun a => y a t)
    (hc : ∀ a, ContinuousOn (fun t => x a t - y a t) (Set.Ici 0)) :
    Measurable fun a => meetingTime (x a) (y a) := by
  apply measurable_of_Iic
  intro c
  by_cases hctop : c = ⊤
  · subst hctop
    simp
  · set s := c.toReal with hsdef
    have hs : 0 ≤ s := ENNReal.toReal_nonneg
    have hc' : c = ENNReal.ofReal s := (ENNReal.ofReal_toReal hctop).symm
    have hset : (fun a => meetingTime (x a) (y a)) ⁻¹' Set.Iic c =
        ⋂ k : ℕ, ⋃ q : ℚ, ({_a : α | 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s} ∩
          {a | |x a q - y a q| < 1 / ((k : ℝ) + 1)}) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hc', meetingTime_le_ofReal_iff (hc a) hs, exists_zero_iff_rat (hc a) hs]
      simp only [and_assoc]
    rw [hset]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => ?_
    refine (MeasurableSet.const _).inter ?_
    exact measurableSet_lt (((hxm q).sub (hym q)).abs) measurable_const

/-- Measurability of the meeting time on the product space, for every orientation pair and
every two mixed strategies. -/
theorem measurable_meetingTime (S₁ S₂ : MixedStrategy) (b₁ b₂ : Bool) :
    Measurable fun p : S₁.Ω × S₂.Ω =>
      meetingTime (fun t => orient b₁ * S₁.path p.1 t)
        (fun t => 2 + orient b₂ * S₂.path p.2 t) := by
  have hx : ∀ t : ℝ, Measurable fun p : S₁.Ω × S₂.Ω => orient b₁ * S₁.path p.1 t :=
    fun t => ((S₁.path_measurable t).comp measurable_fst).const_mul _
  have hy : ∀ t : ℝ, Measurable fun p : S₁.Ω × S₂.Ω => 2 + orient b₂ * S₂.path p.2 t :=
    fun t => (((S₂.path_measurable t).comp measurable_snd).const_mul _).const_add _
  have hc : ∀ p : S₁.Ω × S₂.Ω, ContinuousOn
      (fun t => orient b₁ * S₁.path p.1 t - (2 + orient b₂ * S₂.path p.2 t)) (Set.Ici 0) := by
    intro p
    have h1 := continuousOn_of_feasible (S₁.path_feasible p.1)
    have h2 := continuousOn_of_feasible (S₂.path_feasible p.2)
    exact (continuousOn_const.mul h1).sub (continuousOn_const.add (continuousOn_const.mul h2))
  exact measurable_meetingTime_of (α := S₁.Ω × S₂.Ω)
    (fun p t => orient b₁ * S₁.path p.1 t) (fun p t => 2 + orient b₂ * S₂.path p.2 t) hx hy hc

/-! ### Part L3: integration -/

theorem lower_bound : 13 / 4 ≤ asymmetricRendezvousValue := by
  unfold asymmetricRendezvousValue
  refine le_iInf₂ fun S₁ S₂ => ?_
  unfold expectedMeetingTime
  set μ : Measure (S₁.Ω × S₂.Ω) := S₁.P.prod S₂.P with hμ
  have hsum : ∑ b₁ : Bool, ∑ b₂ : Bool,
      ∫⁻ p, meetingTime (fun t => orient b₁ * S₁.path p.1 t)
        (fun t => 2 + orient b₂ * S₂.path p.2 t) ∂μ =
      ∫⁻ p, ∑ b₁ : Bool, ∑ b₂ : Bool, meetingTime (fun t => orient b₁ * S₁.path p.1 t)
        (fun t => 2 + orient b₂ * S₂.path p.2 t) ∂μ := by
    rw [lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun b₁ _ => ?_
      rw [lintegral_finsetSum]
      intro b₂ _
      exact measurable_meetingTime S₁ S₂ b₁ b₂
    · intro b₁ _
      exact Finset.measurable_sum _ fun b₂ _ => measurable_meetingTime S₁ S₂ b₁ b₂
  rw [hsum]
  have hint : (13 : ENNReal) ≤ ∫⁻ p, ∑ b₁ : Bool, ∑ b₂ : Bool,
      meetingTime (fun t => orient b₁ * S₁.path p.1 t)
        (fun t => 2 + orient b₂ * S₂.path p.2 t) ∂μ := by
    calc (13 : ENNReal) = ∫⁻ _p, (13 : ENNReal) ∂μ := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono fun p =>
          sum_meeting_ge _ _ (S₁.path_feasible p.1) (S₂.path_feasible p.2)
  calc (13 / 4 : ENNReal) = 1 / 4 * 13 := by
        rw [div_eq_mul_inv, one_div, mul_comm]
    _ ≤ _ := by gcongr

end SymmetricRendezvousLine.AG

open SymmetricRendezvousLine in
/-- **Alpern–Gal (1995).** The asymmetric rendezvous value on the line, with initial
distance `2` and unknown orientations, equals `13 / 4`. -/
theorem solution : asymmetricRendezvousValue = 13 / 4 :=
  le_antisymm SymmetricRendezvousLine.AG.upper_bound SymmetricRendezvousLine.AG.lower_bound
