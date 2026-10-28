-- Prove2me | solution 1 for PTCommutant.OperatorBasis.ptLast_swapLast
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:03:11.013347+00:00
-- url     : https://prove2.me/submissions/2aca4889-aaed-4b98-b3ab-dbe3a8cffc26

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

open QAlgorithms.Schur PTCommutant.OperatorBasis

theorem solution {m d : ℕ} (x y : Site d (m + 2)) :
    ptLast (tensorPermutation d (m + 2) (swapLast m)) x y =
      if (∀ i : Fin m, x (Fin.castLE (by omega) i) = y (Fin.castLE (by omega) i)) ∧
          x ⟨m, by omega⟩ = x (Fin.last (m + 1)) ∧ y ⟨m, by omega⟩ = y (Fin.last (m + 1))
        then 1 else 0 := by
  unfold ptLast tensorPermutation swapLast
  simp only [Matrix.of_apply, Equiv.symm_swap]
  have hmL : (⟨m, by omega⟩ : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    simp [Fin.ext_iff]
  congr 1
  apply propext
  rw [funext_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have hi1 : (Fin.castLE (by omega) i : Fin (m + 2)) ≠ Fin.last (m + 1) := by
        simp [Fin.ext_iff]; omega
      have hi2 : (Fin.castLE (by omega) i : Fin (m + 2)) ≠ ⟨m, by omega⟩ := by
        simp [Fin.ext_iff]; omega
      have := h (Fin.castLE (by omega) i)
      rwa [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hi2 hi1, Function.update_of_ne hi1,
        Function.update_of_ne hi1] at this
    · have := h ⟨m, by omega⟩
      rwa [Function.comp_apply, Equiv.swap_apply_left, Function.update_of_ne hmL,
        Function.update_self] at this
    · have := h (Fin.last (m + 1))
      rw [Function.comp_apply, Equiv.swap_apply_right, Function.update_self,
        Function.update_of_ne hmL] at this
      exact this.symm
  · rintro ⟨h1, h2, h3⟩ j
    rw [Function.comp_apply]
    by_cases hjL : j = Fin.last (m + 1)
    · subst hjL
      rw [Equiv.swap_apply_right, Function.update_self, Function.update_of_ne hmL]; exact h3.symm
    by_cases hjm : j = ⟨m, by omega⟩
    · subst hjm
      rw [Equiv.swap_apply_left, Function.update_of_ne hmL, Function.update_self]; exact h2
    rw [Equiv.swap_apply_of_ne_of_ne hjm hjL, Function.update_of_ne hjL, Function.update_of_ne hjL]
    have hj : j.val < m := by
      have h1' : j.val ≠ m + 1 := fun e => hjL (Fin.ext (by simpa using e))
      have h2' : j.val ≠ m := fun e => hjm (Fin.ext e)
      omega
    have := h1 ⟨j.val, hj⟩
    have e : (Fin.castLE (by omega) ⟨j.val, hj⟩ : Fin (m + 2)) = j := Fin.ext rfl
    rwa [e] at this
