-- Prove2me | solution 1 for PermBlockchain.Failure.proposition_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:34.283418+00:00
-- url     : https://prove2.me/submissions/cf05cf81-d8c6-4020-a229-5c5579fd130d

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

open PermBlockchain.Failure in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) :
    ¬ M.IsEquilibrium Scenario.F.profile ∧ ¬ M.IsEquilibrium Scenario.P.profile := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hM.two_le_m
  let i : Mfr m := (0, true, ⟨0, hm⟩)
  have hi : (Scenario.P.profile : Mfr m → Bool) i = true := rfl
  have hpos := hM.χ_pos i
  constructor
  · intro h
    have := h i false
    simp [Model.payoff, Model.grossProfit, Scenario.profile] at this
    linarith
  · intro h
    have := h i false
    simp [Model.payoff, Model.grossProfit, Scenario.profile, i] at this
    linarith
