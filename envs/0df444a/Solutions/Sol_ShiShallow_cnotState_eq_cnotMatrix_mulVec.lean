-- Prove2me | solution 1 for ShiShallow.cnotState_eq_cnotMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T18:22:58.980005+00:00
-- url     : https://prove2.me/submissions/e8ec6a68-de67-4ade-9403-01ea3694e4e0

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow
open Matrix

private theorem shiBrc_cnot_col_unique {n : ℕ} (i j : Fin n) (y z : Bits n)
    (h1 : ∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k)
    (h2 : z i = y i) (h3 : z j = xor (y j) (y i)) :
    z = Function.update y j (xor (y j) (y i)) := by
  funext k
  by_cases hkj : k = j
  · rw [hkj, Function.update_self]
    exact h3
  · rw [Function.update_of_ne hkj]
    by_cases hki : k = i
    · rw [hki]
      exact h2
    · refine (h1 k ?_).symm
      first
        | (simp [hki, hkj]; done)
        | (simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

theorem solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotState i j hij ψ = cnotMatrix i j *ᵥ ψ := by
  funext y
  have hL : cnotState i j hij ψ y = ψ (Function.update y j (xor (y j) (y i))) := rfl
  have hR : (cnotMatrix i j *ᵥ ψ) y = ∑ z, cnotMatrix i j y z * ψ z := by
    first
      | (exact Matrix.mulVec_apply_eq_sum _ _ _)
      | rfl
      | (simp only [Matrix.mulVec, dotProduct]; done)
  have hone : cnotMatrix i j y (Function.update y j (xor (y j) (y i))) = 1 := by
    have hcond :
        (∀ k, k ∉ ({i, j} : Finset (Fin n)) →
            y k = Function.update y j (xor (y j) (y i)) k)
          ∧ Function.update y j (xor (y j) (y i)) i = y i
          ∧ Function.update y j (xor (y j) (y i)) j = xor (y j) (y i) := by
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hkj : k ≠ j := by
          intro h
          exact hk (by simp [h])
        exact (Function.update_of_ne hkj (xor (y j) (y i)) y).symm
      · exact Function.update_of_ne hij (xor (y j) (y i)) y
      · exact Function.update_self j (xor (y j) (y i)) y
    first
      | (simp only [cnotMatrix, Matrix.of_apply]; rw [if_pos hcond]; done)
      | (simp only [cnotMatrix, Matrix.of_apply, if_pos hcond]; done)
      | (simp [cnotMatrix, hcond.1, hcond.2.1, hcond.2.2]; done)
  have hzero : ∀ z ∈ (Finset.univ : Finset (Bits n)),
      z ≠ Function.update y j (xor (y j) (y i)) →
      cnotMatrix i j y z * ψ z = 0 := by
    intro z _ hz
    have hg : ¬ ((∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k) ∧ z i = y i
        ∧ z j = xor (y j) (y i)) := fun hguard =>
      hz (shiBrc_cnot_col_unique i j y z hguard.1 hguard.2.1 hguard.2.2)
    have hent : cnotMatrix i j y z = 0 := by
      first
        | (simp only [cnotMatrix, Matrix.of_apply]; rw [if_neg hg]; done)
        | (simp only [cnotMatrix, Matrix.of_apply, if_neg hg]; done)
        | (simp [cnotMatrix, hg]; done)
    rw [hent, zero_mul]
  have hsingle : ∑ z, cnotMatrix i j y z * ψ z
      = cnotMatrix i j y (Function.update y j (xor (y j) (y i)))
        * ψ (Function.update y j (xor (y j) (y i))) :=
    Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) hzero
  rw [hL, hR, hsingle, hone, one_mul]
