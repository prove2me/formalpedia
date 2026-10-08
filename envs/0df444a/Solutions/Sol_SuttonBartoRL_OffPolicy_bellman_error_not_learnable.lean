-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.bellman_error_not_learnable
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:51:16.826465+00:00
-- url     : https://prove2.me/submissions/9402c640-7e8c-47a3-aca3-6ebdeed2a3b8

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry
import Definitions.Def_SuttonBartoRL_OffPolicy_BELearnabilityExample

open SuttonBartoRL.OffPolicy
set_option maxHeartbeats 0

@[simp] private theorem feature10 : beFeatures1 0 = ![1, 0] := rfl
@[simp] private theorem feature11 : beFeatures1 1 = ![0, 1] := rfl
@[simp] private theorem feature20 : beFeatures2 0 = ![1, 0] := rfl
@[simp] private theorem feature21 : beFeatures2 1 = ![0, 1] := rfl
@[simp] private theorem feature22 : beFeatures2 2 = ![0, 1] := rfl

private noncomputable def step {S : Type} [Fintype S] (M : MDP S Unit)
    (x : S → Fin 2 → ℝ) (α : S → ℝ) (ro : ℝ × (Fin 2 → ℝ)) : S → ℝ :=
  fun s' => if x s' = ro.2 then ∑ s, α s * M.p s () s' ro.1 else 0

private theorem step_match (α : Fin 2 → ℝ) (β : Fin 3 → ℝ)
    (h0 : α 0 = β 0) (h1 : α 1 = 2 * β 1) (h2 : β 2 = β 1)
    (ro : ℝ × (Fin 2 → ℝ)) :
    step beMRP1 beFeatures1 α ro 0 = step beMRP2 beFeatures2 β ro 0 ∧
    step beMRP1 beFeatures1 α ro 1 = 2 * step beMRP2 beFeatures2 β ro 1 ∧
    step beMRP2 beFeatures2 β ro 2 = step beMRP2 beFeatures2 β ro 1 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  all_goals simp +decide [step, beMRP1, beMRP2,
    Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val, h0, h1, h2]
  all_goals split_ifs <;> norm_num <;> ring

private theorem fold_match (l : List (ℝ × (Fin 2 → ℝ)))
    (α : Fin 2 → ℝ) (β : Fin 3 → ℝ)
    (h0 : α 0 = β 0) (h1 : α 1 = 2 * β 1) (h2 : β 2 = β 1) :
    ∑ s, (l.foldl (step beMRP1 beFeatures1) α) s =
      ∑ s, (l.foldl (step beMRP2 beFeatures2) β) s := by
  induction l generalizing α β with
  | nil => simp [Fin.sum_univ_two, Fin.sum_univ_three, h0, h1, h2]; ring
  | cons ro l ih =>
    obtain ⟨g0, g1, g2⟩ := step_match α β h0 h1 h2 ro
    exact ih _ _ g0 g1 g2

private theorem zero_error (γ : ℝ) :
    bellmanError beMRP1 (mrpPolicy (Fin 2)) γ beFeatures1 0 = 0 := by
  funext s
  fin_cases s <;>
    norm_num [bellmanError, bellmanOp, vw, Matrix.mulVec, dotProduct,
      beMRP1, mrpPolicy, Fin.sum_univ_two]

private theorem zero_BE (γ : ℝ) (μ : Fin 2 → ℝ) :
    BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 0 = 0 := by
  simp [BE, zero_error, muNormSq]

theorem solution (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (bellmanError beMRP1 (mrpPolicy (Fin 2)) γ beFeatures1 0 = 0 ∧
      ∀ μ : Fin 2 → ℝ, BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 0 = 0) ∧
    (∀ μ : Fin 2 → ℝ, (∀ s, 0 ≤ μ s) → ∀ w : Fin 2 → ℝ,
      BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 0
        ≤ BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 w) ∧
    BE beMRP2 (mrpPolicy (Fin 3)) γ beMu2 beFeatures2 0 = 2 / 3 ∧
    (∀ s' : Fin 3, ∑ s, beMu2 s * beMRP2.trans s () s' = beMu2 s') ∧
    (∀ s' : Fin 2, ∑ s, beMu1 s * beMRP1.trans s () s' = beMu1 s') ∧
    ∀ (o₀ : Fin 2 → ℝ) (l : List (ℝ × (Fin 2 → ℝ))),
      obsProb beMRP1 beMu1 beFeatures1 o₀ l = obsProb beMRP2 beMu2 beFeatures2 o₀ l := by
  classical
  refine ⟨⟨zero_error γ, zero_BE γ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ hμ w
    rw [zero_BE]
    change 0 ≤ ∑ s, μ s * (bellmanError beMRP1 (mrpPolicy (Fin 2)) γ beFeatures1 w s) ^ 2
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  · simp +decide [BE, muNormSq, bellmanError, bellmanOp, vw, Matrix.mulVec, dotProduct,
      beMRP2, beMu2, mrpPolicy, Fin.sum_univ_two, Fin.sum_univ_three] <;> norm_num
  · intro s'; fin_cases s' <;>
      simp +decide [MDP.trans, beMRP2, beMu2, Fin.sum_univ_three, Finset.filter_insert, Finset.filter_singleton] <;> norm_num
  · intro s'; fin_cases s' <;>
      simp +decide [MDP.trans, beMRP1, beMu1, Fin.sum_univ_two] <;> norm_num
  · intro o₀ l
    apply fold_match
    · simp [beMu1, beMu2]
    · simp [beMu1, beMu2]
      split_ifs <;> norm_num
    · simp [beMu2]


#print axioms solution
