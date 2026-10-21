-- Prove2me | solution 1 for RobustPower.SimplexGap.robust_value_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:30:27.184985+00:00
-- url     : https://prove2.me/submissions/29d082fe-8d75-408a-a0ab-a96473924365

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

set_option autoImplicit false

open RobustPower.SimplexGap

theorem solution (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} (b : Ω → Fin n → ℝ)
    (hb : Set.range b = cornerSimplex n) :
    (∀ (x : Fin 0 → ℝ) (y : Fin n → ℝ),
        RobFeasible (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ x y →
          ∀ j, 1 ≤ y j) ∧
      (1 : EReal) ≤ zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Fin 0 → ℝ) (lastUnit n) b ∅ ∅ := by
  have key : ∀ (x : Fin 0 → ℝ) (y : Fin n → ℝ),
        RobFeasible (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ x y →
          ∀ j, 1 ≤ y j := by
    intro x y hf j
    obtain ⟨-, -, h⟩ := hf
    have hx : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ cornerSimplex n := by
      refine ⟨?_, ?_⟩
      · simp
      · intro i; by_cases h : i = j <;> simp [Pi.single_apply, h]
    rw [← hb] at hx
    obtain ⟨ω, hω⟩ := hx
    have := h ω j
    rw [hω] at this
    simpa using this
  refine ⟨key, ?_⟩
  unfold zRob
  refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
  have hj := key x y hf ⟨n - 1, by omega⟩
  have hd : lastUnit n ⬝ᵥ y = y ⟨n - 1, by omega⟩ := by
    unfold dotProduct
    rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
    · simp [lastUnit]
    · intro j _ hj
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      simp [lastUnit, this]
    · simp
  have h0 : (0 : Fin 0 → ℝ) ⬝ᵥ x = 0 := by simp
  rw [hd, h0]
  have : (1 : ℝ) ≤ 0 + y ⟨n - 1, by omega⟩ := by linarith
  exact_mod_cast this
