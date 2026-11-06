-- Prove2me | solution 1 for SchmidliRuin.Verif.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:16:25.473585+00:00
-- url     : https://prove2.me/submissions/bcd9e734-5b9e-4c6d-9d47-19595cc0f6f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model
import Theorems.Thm_SchmidliRuin_Verif_survival_le_and_eq
import Theorems.Thm_SchmidliRuin_Verif_near_optimal_strategy_exists

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

open SchmidliRuin.Verif

theorem solution {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω) (hB : B.IsValid)
    (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf_neg : ∀ x < 0, f x = 0) (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf_mono : StrictMonoOn f (Ici 0)) (hf_cont : ContinuousOn f (Ici 0))
    (hf_C2 : ContDiffOn ℝ 2 f (Ioi 0))
    (hf_hjb : ∀ u > 0, SolvesHJB c B.lam mu sigma cb B.ν f u) :
    BddAbove (f '' Ici 0) ∧
    (∃ L : ℝ, 0 < L ∧ Tendsto f atTop (𝓝 L) ∧
      ∀ u, 0 ≤ u → valueFn B c mu sigma cb u = f u / L) ∧
    (∀ bstar : ℝ → ℝ, IsBStar c B.lam cb B.ν f bstar →
      ∀ u, 0 < u → ∀ A b X : ℝ≥0 → Ω → ℝ,
        IsAdmissible B c mu sigma cb u A b X → FollowsFeedback mu sigma f bstar u A b X →
        survivalProb B X = valueFn B c mu sigma cb u) := by
  have hf : IsHJBSolution c B.lam mu sigma cb B.ν f :=
    ⟨hf_neg, hf_nonneg, hf_mono, hf_cont, hf_C2, hf_hjb⟩
  obtain ⟨L, hL0, hL, hle, heq⟩ :=
    survival_le_and_eq B hB c mu sigma hc hmu hsigma cb hcb f hf
  have : IsProbabilityMeasure B.P := hB.1
  -- the value function equals f u / L
  have hval : ∀ u, 0 ≤ u → valueFn B c mu sigma cb u = f u / L := by
    intro u hu
    have hbdd : BddAbove {p | ∃ A b X : ℝ≥0 → Ω → ℝ, IsAdmissible B c mu sigma cb u A b X ∧
        p = survivalProb B X} := by
      refine ⟨1, ?_⟩
      rintro p ⟨A, b, X, -, rfl⟩
      unfold survivalProb
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    obtain ⟨A0, b0, X0, h0, -⟩ :=
      near_optimal_strategy_exists B hB c mu sigma hc hmu hsigma cb hcb f hf L hL u hu 1
        one_pos
    apply le_antisymm
    · unfold valueFn
      refine csSup_le ⟨survivalProb B X0, A0, b0, X0, h0, rfl⟩ ?_
      rintro p ⟨A, b, X, hadm, rfl⟩
      exact hle u hu A b X hadm
    · apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨A, b, X, hadm, hlt⟩ :=
        near_optimal_strategy_exists B hB c mu sigma hc hmu hsigma cb hcb f hf L hL u hu ε hε
      have : survivalProb B X ≤ valueFn B c mu sigma cb u :=
        le_csSup hbdd ⟨A, b, X, hadm, rfl⟩
      linarith
  refine ⟨?_, ⟨L, hL0, hL, hval⟩, ?_⟩
  · refine ⟨L, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply ge_of_tendsto hL
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hf_mono.monotoneOn hx (le_trans (show (0:ℝ) ≤ x from hx) hy) hy
  · intro bstar hbstar u hu A b X hadm hfb
    rw [heq bstar hbstar u hu A b X hadm hfb, hval u hu.le]
