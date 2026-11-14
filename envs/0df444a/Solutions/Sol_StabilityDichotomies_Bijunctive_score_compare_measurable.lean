-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.score_compare_measurable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:20:19.652205+00:00
-- url     : https://prove2.me/submissions/7034f7b1-7836-41b4-b135-ba96474751ae

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem score_lt_shift_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (target root : Literal V) (n : ℕ) :
    MeasurableSet {δ : Literal V → ℝ |
      literalScore rep G F δ target < ((δ root - n : ℝ) : WithBot ℝ)} := by
  have hform : {δ : Literal V → ℝ |
      literalScore rep G F δ target < ((δ root - n : ℝ) : WithBot ℝ)} =
      ⋂ r : Literal V, {δ : Literal V → ℝ |
        (if feasibleLiteral F r then
          match implicationDistance rep G r target with
          | some k => ((δ r - k : ℝ) : WithBot ℝ)
          | none => ⊥
        else ⊥) < ((δ root - n : ℝ) : WithBot ℝ)} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    unfold literalScore
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe (δ root - n))]
    simp only [Finset.mem_univ, true_implies]
    constructor <;> intro h r
    all_goals
      have hh := h r
      rw [lt_iff_le_not_ge] at hh ⊢
      exact hh
  rw [hform]
  apply MeasurableSet.iInter
  intro r
  by_cases hr : feasibleLiteral F r
  · cases hd : implicationDistance rep G r target with
    | none => simp [hr,hd]
    | some k =>
      have hm : MeasurableSet {δ : Literal V → ℝ | δ r - k < δ root - n} :=
        measurableSet_lt ((measurable_pi_apply (X := fun _ : Literal V => ℝ) r).sub_const (k : ℝ))
          ((measurable_pi_apply (X := fun _ : Literal V => ℝ) root).sub_const (n : ℝ))
      simpa [hr,hd] using hm
  · simp [hr]

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (a b : Literal V) :
    MeasurableSet {δ : Literal V → ℝ | literalScore rep G F δ b < literalScore rep G F δ a} := by
  have hform : {δ : Literal V → ℝ | literalScore rep G F δ b < literalScore rep G F δ a} =
      ⋃ r : Literal V, {δ : Literal V → ℝ |
        literalScore rep G F δ b < (if feasibleLiteral F r then
          match implicationDistance rep G r a with
          | some k => ((δ r - k : ℝ) : WithBot ℝ)
          | none => ⊥
        else ⊥)} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    unfold literalScore at *
    rw [Finset.lt_sup_iff]
    simp only [Finset.mem_univ, true_and]
    constructor <;> rintro ⟨r,hr⟩ <;> refine ⟨r, ?_⟩
    all_goals
      rw [lt_iff_le_not_ge] at hr ⊢
      exact hr
  rw [hform]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : feasibleLiteral F r
  · cases hd : implicationDistance rep G r a with
    | none => simp [hr,hd]
    | some k => simpa [hr,hd] using score_lt_shift_measurable rep G F b r k
  · simp [hr]

