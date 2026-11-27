-- Prove2me | solution 1 for ShipConsol.OneWH.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:02.824298+00:00
-- url     : https://prove2.me/submissions/58d75a5c-8ee2-4866-8ed9-151344db9a44

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_FixedRun

open ShipConsol
open ShipConsol.OneWH
open ShipConsol.OneWH.Supplement

theorem solution (F : ℝ → ℝ) (hF : CostAssumptions F)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (d τ : ℕ) (hd : 1 ≤ d) (hτ : 1 ≤ τ ∧ τ ≤ d) :
    Filter.Tendsto (fun T : ℕ => fixedExpectedAverage F α d τ T)
      Filter.atTop (nhds (fixedCriterion F α d τ)) := by
        obtain ⟨hα0, hα1⟩ := hα
        obtain ⟨hτ1, hτd⟩ := hτ
        obtain ⟨_, hanti, hnn⟩ := hF
        have Wnone : ∀ t, fixedPolicyTotal F α d τ (t + 1) none =
            α * fixedPolicyTotal F α d τ t (some d) +
            (1 - α) * fixedPolicyTotal F α d τ t none := by
          intro t
          simp [fixedPolicyTotal]
        have W1 : ∀ z, fixedPolicyTotal F α d τ 1 (some z) = F z := by
          intro z
          simp [fixedPolicyTotal]
        have Wship : ∀ t z, z ≤ τ → fixedPolicyTotal F α d τ (t + 1) (some z) =
            F z + α * fixedPolicyTotal F α d τ t (some d) +
            (1 - α) * fixedPolicyTotal F α d τ t none := by
          intro t z hz
          simp [fixedPolicyTotal, hz]
        have Whold : ∀ t z, τ < z → z ≤ d → fixedPolicyTotal F α d τ (t + 2) (some z) =
            fixedPolicyTotal F α d τ (t + 1) (some (z - 1)) := by
          intro t z hz hzd
          have h1 : ¬ z ≤ τ := by omega
          have h2 : min d (z - 1) = z - 1 := by omega
          rw [fixedPolicyTotal]
          simp only [Option.isSome_some, Option.getD_some, h1, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, or_false, if_false, Option.map_some, h2, true_and]
          ring
        rcases hα0.eq_or_lt with h0 | hpos
        · subst h0
          have hz : ∀ t, fixedPolicyTotal F 0 d τ t none = 0 := by
            intro t
            induction t with
            | zero => rfl
            | succ t ih => rw [Wnone, ih]; ring
          have : (fun T : ℕ => fixedExpectedAverage F 0 d τ T) = fun _ => 0 := by
            funext T
            simp [fixedExpectedAverage, hz]
          rw [this]
          simp [fixedCriterion]
        · have hdτ : (τ : ℝ) ≤ d := by exact_mod_cast hτd
          have hτ1' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
          have hF0 : ∀ z : ℕ, 1 ≤ z → 0 ≤ F z ∧ F z ≤ F 1 := by
            intro z hz
            have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
            exact ⟨hnn z hz', hanti (by simp) hz' hz'⟩
          have hinv : 0 < 1 / α := by positivity
          have hden : 0 < 1 / α + (d : ℝ) - τ := by linarith
          obtain ⟨g, hg⟩ : ∃ g, g = fixedCriterion F α d τ := ⟨_, rfl⟩
          have hgeq : g = F τ / (1 / α + (d : ℝ) - τ) := by
            rw [hg, fixedCriterion, if_neg hpos.ne']
          have hg0 : 0 ≤ g := by
            rw [hgeq]; exact div_nonneg (hF0 τ hτ1).1 hden.le
          have hgmul : g * (1 / α + (d : ℝ) - τ) = F τ := by
            rw [hgeq]; exact div_mul_cancel₀ _ hden.ne'
          obtain ⟨b, hb⟩ : ∃ b, b = g * (1 / α) := ⟨_, rfl⟩
          have hb0 : 0 ≤ b := by rw [hb]; positivity
          have hαb : α * b = g := by rw [hb]; field_simp
          have hFτ : F τ = b + d * g - τ * g := by rw [← hgmul, hb]; ring
          obtain ⟨C, hC⟩ : ∃ C, C = F 1 + g + b + d * g := ⟨_, rfl⟩
          have hF1 : 0 ≤ F 1 := by simpa using (hF0 1 le_rfl).1
          have hdg : 0 ≤ (d : ℝ) * g := by positivity
          have key : ∀ t : ℕ,
              |fixedPolicyTotal F α d τ (t + 1) none - ((t : ℝ) + 1) * g| ≤ C ∧
              ∀ z : ℕ, τ ≤ z → z ≤ d →
                |fixedPolicyTotal F α d τ (t + 1) (some z) - ((t : ℝ) + 1) * g
                  - (b + ((d : ℝ) - z) * g)| ≤ C := by
            intro t
            induction t with
            | zero =>
              refine ⟨?_, ?_⟩
              · rw [Wnone]
                simp only [fixedPolicyTotal, Nat.cast_zero]
                rw [abs_le]; constructor <;> linarith
              · intro z hz hzd
                rw [W1]
                have hz1 := hF0 z (by omega)
                have hzd' : (z : ℝ) ≤ d := by exact_mod_cast hzd
                have h1 : 0 ≤ ((d : ℝ) - z) * g := mul_nonneg (by linarith) hg0
                have h2 : 0 ≤ (z : ℝ) * g := by positivity
                simp only [Nat.cast_zero]
                rw [abs_le]; constructor <;> linarith
            | succ t ih =>
              obtain ⟨ihn, ihz⟩ := ih
              have ihd := ihz d hτd le_rfl
              have comb : |α * (fixedPolicyTotal F α d τ (t + 1) (some d) - ((t : ℝ) + 1) * g
                    - (b + ((d : ℝ) - d) * g)) +
                  (1 - α) * (fixedPolicyTotal F α d τ (t + 1) none - ((t : ℝ) + 1) * g)| ≤ C := by
                rw [abs_le] at *
                have a1 := mul_le_mul_of_nonneg_left ihd.1 hα0
                have a2 := mul_le_mul_of_nonneg_left ihd.2 hα0
                have a3 := mul_le_mul_of_nonneg_left ihn.1 (sub_nonneg.2 hα1)
                have a4 := mul_le_mul_of_nonneg_left ihn.2 (sub_nonneg.2 hα1)
                constructor <;> linarith
              refine ⟨?_, ?_⟩
              · rw [Wnone]
                convert comb using 2
                push_cast
                linear_combination hαb
              · intro z hz hzd
                rcases hz.eq_or_lt with rfl | hlt
                · rw [Wship _ _ le_rfl]
                  convert comb using 2
                  push_cast
                  linear_combination hFτ + hαb
                · rw [Whold _ _ hlt hzd]
                  convert ihz (z - 1) (by omega) (by omega) using 2
                  rw [Nat.cast_sub (by omega : 1 ≤ z)]
                  push_cast
                  ring
          rw [← hg, tendsto_iff_dist_tendsto_zero]
          refine squeeze_zero' (g := fun T : ℕ => C / (T : ℝ))
            (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_
            (tendsto_const_div_atTop_nhds_zero_nat C)
          filter_upwards [Filter.eventually_ge_atTop 1] with T hT
          obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
          have hk := (key t).1
          have hTpos : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by positivity
          have e : fixedExpectedAverage F α d τ (t + 1) - g =
              (fixedPolicyTotal F α d τ (t + 1) none - ((t : ℝ) + 1) * g) / ((t + 1 : ℕ) : ℝ) := by
            rw [fixedExpectedAverage]
            have : (t : ℝ) + 1 = ((t + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [this]
            field_simp
          rw [Real.dist_eq, e, abs_div, abs_of_pos hTpos]
          exact div_le_div_of_nonneg_right hk hTpos.le
