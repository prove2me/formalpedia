-- Prove2me | solution 1 for RainbowEFX.Sublinear.count_at_termination
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:50:18.682342+00:00
-- url     : https://prove2.me/submissions/08c71a07-b0f5-45d0-a497-ddf4f424a6e1

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting
import Theorems.Thm_RainbowEFX_Sublinear_observation_12

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hd : 1 ≤ d) (hstar : Star ε v X) (hL : (LX ε v X d).card ≤ d ^ 4 + d) :
    ((pool X).card : ℝ) ≤ 2 * max (2 * n / (ε * d)) (2 * (d : ℝ) ^ 4) := by
  classical
  have hH := observation_12 hn v hv ε hε0 hε X hX hEFX d hd hstar
  have hsplit : (pool X).card = (HX ε v X d).card + (LX ε v X d).card := by
    unfold HX LX
    rw [← Finset.card_filter_add_card_filter_not (s := pool X)
      (p := fun g => d < (valuableAgents ε v X g).card)]
    congr 2
    ext g; simp
  have hLr : ((LX ε v X d).card : ℝ) ≤ (d : ℝ) ^ 4 + d := by exact_mod_cast hL
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd4 : (d : ℝ) ≤ (d : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
    nlinarith
  rw [hsplit]; push_cast
  have h1 := le_max_left (2 * (n : ℝ) / (ε * d)) (2 * (d : ℝ) ^ 4)
  have h2 := le_max_right (2 * (n : ℝ) / (ε * d)) (2 * (d : ℝ) ^ 4)
  linarith
