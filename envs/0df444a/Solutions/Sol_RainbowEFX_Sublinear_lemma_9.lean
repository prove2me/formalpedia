-- Prove2me | solution 1 for RainbowEFX.Sublinear.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:53:17.507267+00:00
-- url     : https://prove2.me/submissions/cb966384-2940-4f1b-a48f-395b315de342

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting
import Theorems.Thm_RainbowEFX_Sublinear_observation_7

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (hU2 : ∃ i, HeavilyEnvies ε v X i (pool X)) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by
  classical
  obtain ⟨t, Z, hZP, htZ, hno⟩ := (observation_7 v hv ε hε0 hε1 X (pool X)).1 hU2
  have hZ0 : 0 ≤ v t Z := hv.2 _ _
  have htle : v t (X t) ≤ v t Z := by
    have : (1 - ε) * v t Z ≤ v t Z := by nlinarith
    exact (le_of_lt htZ).trans this
  have hZX : ∀ j, Disjoint Z (X j) := by
    intro j
    rw [Finset.disjoint_left]
    intro x hxZ hxX
    have := hZP hxZ
    simp only [pool, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
      not_exists] at this
    exact this j hxX
  have hval : ∀ i, v i (X i) ≤ v i (Function.update X t Z i) := by
    intro i
    by_cases h : i = t
    · subst h; simpa using htle
    · simp [h]
  refine ⟨Function.update X t Z, ?_, ?_, hval, t, by simpa [HeavilyEnvies] using htZ⟩
  · intro i j hij
    by_cases hi : i = t
    · subst hi
      have hj : j ≠ i := fun h => hij h.symm
      simp only [Function.update_self, Function.update_of_ne hj]
      exact hZX j
    · by_cases hj : j = t
      · subst hj
        simp only [Function.update_self, Function.update_of_ne hi]
        exact (hZX i).symm
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
        exact hX hij
  · intro i j g hg
    by_cases hj : j = t
    · subst hj
      simp only [Function.update_self] at hg ⊢
      have hlt : Z.erase g ⊂ Z := Finset.erase_ssubset hg
      have := hno i
      simp only [StronglyEnvies, HeavilyEnvies, not_exists, not_and, not_lt] at this
      exact (this _ hlt).trans (hval i)
    · simp only [Function.update_of_ne hj] at hg ⊢
      exact (hEFX i j g hg).trans (hval i)
