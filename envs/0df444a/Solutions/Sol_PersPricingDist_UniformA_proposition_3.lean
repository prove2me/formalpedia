-- Prove2me | solution 1 for PersPricingDist.UniformA.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:44:59.388572+00:00
-- url     : https://prove2.me/submissions/35664632-0300-429a-9abb-1a4b850209fe

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting
import Theorems.Thm_PersPricingDist_UniformA_mono_uniform
import Theorems.Thm_PersPricingDist_UniformA_uu_retail_equilibrium
import Theorems.Thm_PersPricingDist_UniformA_uu_profit_12
import Theorems.Thm_PersPricingDist_UniformA_up_leader_equilibrium
import Theorems.Thm_PersPricingDist_UniformA_up_profit_14
import Theorems.Thm_PersPricingDist_UniformA_profit_gap_15

open PersPricingDist.UniformA

theorem solution (M : Model) (hM : M.Standing) :
    (∃ w : ℝ, 0 ≤ w ∧ (∃ pA pB : ℝ, M.IsNashUU w pA pB) ∧
      ∀ pA pB : ℝ, M.IsNashUU w pA pB →
        ∀ p : ℝ, M.monoProfitU p < M.indUU pA pB) ∧
    (∃ w : ℝ, 0 ≤ w ∧ (∃ pA : ℝ, M.IsLeaderOptUP w pA) ∧
      ∀ pA : ℝ, M.IsLeaderOptUP w pA →
        ∀ p : ℝ, M.monoProfitU p < M.indUP w pA) := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  obtain ⟨hmono, -⟩ := mono_uniform M hM
  obtain ⟨hNash, huniq⟩ := uu_retail_equilibrium M hM
  obtain ⟨h12, -, h12pos⟩ := uu_profit_12 M hM
  obtain ⟨hLead, hLuniq⟩ := up_leader_equilibrium M hM
  have h14 := up_profit_14 M hM
  obtain ⟨h15, h15pos⟩ := profit_gap_15 M hM
  refine ⟨⟨M.wUU, ?_, ⟨_, _, hNash⟩, ?_⟩, ⟨M.wUP, ?_, ⟨_, hLead⟩, ?_⟩⟩
  · unfold Model.wUU
    apply div_nonneg
    · have : 0 ≤ 4 * (1 + M.v) + M.s := by linarith
      positivity
    · linarith
  · intro pA pB h p
    obtain ⟨rfl, rfl⟩ := huniq pA pB h
    linarith [hmono p]
  · unfold Model.wUP
    apply div_nonneg
    · have : 0 ≤ 1 + M.v := by linarith
      positivity
    · linarith
  · intro pA h p
    obtain rfl := hLuniq pA h
    rw [h14]
    linarith [hmono p]
