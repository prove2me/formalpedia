-- Prove2me | solution 1 for PersPricingDist.UniformA.mono_uniform
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:02:40.304892+00:00
-- url     : https://prove2.me/submissions/b33a4f76-fcd8-41e8-acaf-d6d699730ed0

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting
set_option autoImplicit false

open PersPricingDist.UniformA

lemma oo_demand_mono (M : Model) (hM : M.Standing) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    M.demand (M.buysMono p) = 1 - p := by
  have hX : 1 ≤ M.X := by
    have h1 : 1 < M.v / M.s := by
      rw [lt_div_iff₀ hM.s_pos]; linarith [hM.s_lt_v]
    linarith [hM.market_large]
  have hset : {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysMono p x} = Set.Icc 0 (1 - p) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Model.buysMono, Model.uA, ge_iff_le]
    constructor
    · rintro ⟨⟨h0, _⟩, h⟩
      refine ⟨h0, ?_⟩
      rcases le_max_iff.1 h with h | h
      · linarith
      · linarith
    · rintro ⟨h0, h⟩
      refine ⟨⟨h0, by linarith⟩, ?_⟩
      exact le_max_of_le_left (by linarith)
  unfold Model.demand
  rw [hset, Real.volume_Icc]
  simp only [sub_zero]
  rw [ENNReal.toReal_ofReal (by linarith)]

theorem solution (M : Model) (hM : M.Standing) :
    (∀ p : ℝ, M.monoProfitU p ≤ (1 : ℝ) / 4) ∧
    M.monoProfitU ((1 : ℝ) / 2) = (1 : ℝ) / 4 := by
  constructor
  · intro p
    unfold Model.monoProfitU
    by_cases hp0 : p ≤ 0
    · have : 0 ≤ M.demand (M.buysMono p) := ENNReal.toReal_nonneg
      nlinarith
    · push_neg at hp0
      by_cases hp1 : p ≤ 1
      · rw [oo_demand_mono M hM p hp0 hp1]
        nlinarith [sq_nonneg (p - 1/2)]
      · push_neg at hp1
        have : M.demand (M.buysMono p) = 0 := by
          unfold Model.demand
          have : {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysMono p x} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_Icc, Model.buysMono, Model.uA, ge_iff_le,
              Set.mem_empty_iff_false, iff_false, not_and]
            intro ⟨h0, _⟩ h
            rcases le_max_iff.1 h with h | h <;> linarith
          rw [this]; simp
        rw [this]; norm_num
  · unfold Model.monoProfitU
    rw [oo_demand_mono M hM (1/2) (by norm_num) (by norm_num)]
    norm_num
