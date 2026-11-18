-- Prove2me | solution 1 for RealPinwheel.FiveSixths.codeCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:13:08.250458+00:00
-- url     : https://prove2.me/submissions/429a3c61-3b9b-4db5-a96c-6891f5d58fc5

import Theorems.Thm_RealPinwheel_FiveSixths_cycleCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CycleCode
open RealPinwheel.FiveSixths

theorem solution {n : ℕ} (hn : 0 < n) (c : CycleCode)
    (hcheck : codeCheck n hn c = true) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : codeBox c (fun i => 1 / a i)) :
    ∃ (L : ℕ) (S : ℕ → Fin n),
      L = (codeWord n hn c).size ∧ Periodic S L ∧ Valid a S := by
  apply cycleCheck_sound (codeWord n hn c) (codeNum c) (codeDen c) (codeStrict c) hcheck a ha
  intro i
  have hh := hb i
  have hL : 0 < (codeWord n hn c).size := by
    by_contra h
    simp [codeCheck, cycleCheck, h] at hcheck
  have hnumden : 0 < codeNum c i ∧ 0 < codeDen c i := by
    unfold codeCheck cycleCheck at hcheck
    rw [dif_pos hL] at hcheck
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_finRange, forall_true_left] at hcheck
    exact (hcheck i).1.1
  have hp : (0 : ℝ) < codeNum c i := by exact_mod_cast hnumden.1
  have hq : (0 : ℝ) < codeDen c i := by exact_mod_cast hnumden.2
  dsimp only [codeBox] at hb
  change (if codeStrict c i = true then (codeDen c i : ℝ) / codeNum c i < a i
    else (codeDen c i : ℝ) / codeNum c i ≤ a i)
  change (if codeStrict c i = true then 1 / a i < (codeNum c i : ℝ) / codeDen c i
    else 1 / a i ≤ (codeNum c i : ℝ) / codeDen c i) at hh
  split_ifs at hh ⊢ with hs
  · rw [div_lt_iff₀ hp]
    have h2 := (div_lt_div_iff₀ (ha i) hq).mp hh
    nlinarith
  · rw [div_le_iff₀ hp]
    have h2 := (div_le_div_iff₀ (ha i) hq).mp hh
    nlinarith
