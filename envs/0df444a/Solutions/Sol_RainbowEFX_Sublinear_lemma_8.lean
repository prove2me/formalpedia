-- Prove2me | solution 1 for RainbowEFX.Sublinear.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:47:37.347049+00:00
-- url     : https://prove2.me/submissions/a1a71b48-d0d0-45b0-99eb-b7f4f9f3af73

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (s : Fin n) (hs : IsSource v X s) (g : Fin m) (hg : g ∈ pool X)
    (hno : ∀ i, ¬ StronglyEnvies ε v X i (insert g (X s))) :
    IsPartialAllocation (Function.update X s (insert g (X s))) ∧
      IsAlphaEFX (1 - ε) v (Function.update X s (insert g (X s))) ∧
      ∀ i, v i (X i) ≤ v i (Function.update X s (insert g (X s)) i) := by
  classical
  have mono : ∀ i (A B : Finset (Fin m)), A ⊆ B → v i A ≤ v i B := by
    intro i A B hAB
    rw [hv.1 i A, hv.1 i B]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hv.2 i {x})
  have hgX : ∀ j, g ∉ X j := by
    intro j hj
    simp only [pool, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
      not_exists, not_and] at hg
    exact hg j hj
  have hsub : ∀ i, X i ⊆ Function.update X s (insert g (X s)) i := by
    intro i
    by_cases h : i = s
    · subst h; simp [Finset.subset_insert]
    · simp [h]
  have hval : ∀ i, v i (X i) ≤ v i (Function.update X s (insert g (X s)) i) :=
    fun i => mono i _ _ (hsub i)
  refine ⟨?_, ?_, hval⟩
  · intro i j hij
    by_cases hi : i = s
    · subst hi
      have hj : j ≠ i := fun h => hij h.symm
      simp only [Function.update_self, Function.update_of_ne hj]
      rw [Finset.disjoint_insert_left]
      exact ⟨hgX j, hX hij⟩
    · by_cases hj : j = s
      · subst hj
        simp only [Function.update_self, Function.update_of_ne hi]
        rw [Finset.disjoint_insert_right]
        exact ⟨hgX i, hX hij⟩
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
        exact hX hij
  · intro i j h hh
    by_cases hj : j = s
    · subst hj
      simp only [Function.update_self] at hh ⊢
      have hlt : (insert g (X j)).erase h ⊂ insert g (X j) := Finset.erase_ssubset hh
      have := hno i
      simp only [StronglyEnvies, HeavilyEnvies, not_exists, not_and, not_lt] at this
      exact (this _ hlt).trans (hval i)
    · simp only [Function.update_of_ne hj] at hh ⊢
      exact (hEFX i j h hh).trans (hval i)
