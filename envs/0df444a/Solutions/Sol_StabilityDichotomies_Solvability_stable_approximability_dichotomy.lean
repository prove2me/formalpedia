-- Prove2me | solution 1 for StabilityDichotomies.Solvability.stable_approximability_dichotomy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:27:47.21926+00:00
-- url     : https://prove2.me/submissions/bf6061b2-5bcd-4696-b230-48b674a3556d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StabilityDichotomies_Solvability_nonwidth_approximation_lower
import Theorems.Thm_StabilityDichotomies_Solvability_boolean_bounded_width_criterion
import Theorems.Thm_StabilityDichotomies_Solvability_valid_language_zero_sensitivity
import Theorems.Thm_StabilityDichotomies_Solvability_horn_dual_horn_approximation_upper
import Theorems.Thm_StabilityDichotomies_Solvability_bijunctive_approximation_upper
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

private theorem valid_upper (Γ : Language) (b : Bool) (hv : Valid Γ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hε1
  obtain ⟨A,hA,hzero⟩ := valid_language_zero_sensitivity Γ b hv ε (le_of_lt hε)
  refine ⟨A,hA,?_⟩
  intro V _ I hI hn
  rw [hzero V I]
  have hnum : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast (by omega : 1 ≤ Fintype.card V)
  have hlog : 0 ≤ Real.log (Fintype.card V : ℝ) := Real.log_nonneg hnum
  positivity

private theorem horn_upper_to_log (Γ : Language)
    (hΓ : (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples) ∨
      (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  obtain ⟨C,hC,hupper⟩ := horn_dual_horn_approximation_upper Γ hΓ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / Real.log 2, div_pos hC hlog, ?_⟩
  intro ε hε hε1
  obtain ⟨A,hA,hbound⟩ := hupper ε hε hε1
  refine ⟨A,hA,?_⟩
  intro V _ I hI hn
  have hnum : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log (Fintype.card V : ℝ) := Real.log_le_log (by norm_num) hnum
  calc
    _ ≤ C * ε⁻¹ := hbound V I hI
    _ = (C / Real.log 2) * ε⁻¹ * Real.log 2 := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogn (mul_nonneg (le_of_lt (div_pos hC hlog)) (inv_nonneg.mpr (le_of_lt hε)))

private theorem width_upper (Γ : Language) (hΓ : BoundedWidth Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  rcases (boolean_bounded_width_criterion Γ).1 hΓ with hzero | hone | hhorn | hdual | hbij
  · exact valid_upper Γ false hzero
  · exact valid_upper Γ true hone
  · exact horn_upper_to_log Γ (Or.inl hhorn)
  · exact horn_upper_to_log Γ (Or.inr hdual)
  · exact bijunctive_approximation_upper Γ hbij

theorem solution (Γ : Language) :
    Xor
      (BoundedWidth Γ ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∃ A : Solver Γ, Approximates A ε ∧
              ∀ (V : Type) [Fintype V] (I : Instance Γ V),
                Satisfiable I → 2 ≤ Fintype.card V →
                  averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ))
      (¬ BoundedWidth Γ ∧
        ∃ ε c : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧
          ∃ N : Set ℕ, N.Infinite ∧
            ∀ A : Solver Γ, Approximates A ε →
              ∀ n ∈ N, ∃ I : Instance Γ (Fin n),
                Satisfiable I ∧ c * n ≤ averageSensitivity A I) := by
  unfold Xor
  by_cases hΓ : BoundedWidth Γ
  · left
    exact ⟨⟨hΓ, width_upper Γ hΓ⟩, fun h => h.1 hΓ⟩
  · right
    exact ⟨⟨hΓ, nonwidth_approximation_lower Γ hΓ⟩, fun h => hΓ h.1⟩
