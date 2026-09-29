-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.fast_forward_selection_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:37:08.553866+00:00
-- url     : https://prove2.me/submissions/081c8724-6711-4107-a654-2a7754487a66

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsFastForwardRun

open ScenarioReduction.ForwardSelection in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) (u : ℕ → Fin N)
    (hrun : IsFastForwardRun (scenCost h ω₀ ω) p n u) :
    IsForwardSelection (scenCost h ω₀ ω) p n u ∧
    ∀ i (hi : i ∈ Finset.Icc 1 n),
      zStep (scenCost h ω₀ ω) p u i (u i) =
        reductionCost (scenCost h ω₀ ω) p (Jstep u i)
          (Jstep_compl_nonempty u (Finset.mem_Icc.1 hi).1) := by
  generalize scenCost h ω₀ ω = c at hrun ⊢
  have inf'_eq : ∀ (A B : Finset (Fin N)) (hA : A.Nonempty) (hB : B.Nonempty)
      (f : Fin N → ℝ), A = B → A.inf' hA f = B.inf' hB f := by
    intro A B hA hB f hAB
    subst hAB
    rfl
  have rc_eq : ∀ (A B : Finset (Fin N)) (hA : Aᶜ.Nonempty) (hB : Bᶜ.Nonempty),
      A = B → reductionCost c p A hA = reductionCost c p B hB := by
    intro A B hA hB hAB
    subst hAB
    rfl
  have hsel0 : sel u 0 = ∅ := by simp [sel]
  have hsel : ∀ i, sel u (i + 1) = insert (u (i + 1)) (sel u i) := by
    intro i
    simp only [sel]
    rw [← Finset.image_insert]
    congr 1
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hkey : ∀ i k v, cStep c u (i + 1) k v =
      (insert v (sel u i)).inf' (Finset.insert_nonempty _ _) (fun j => c k j) := by
    intro i
    induction i with
    | zero =>
      intro k v
      rw [inf'_eq _ {v} _ (Finset.singleton_nonempty v) _ (by rw [hsel0]; rfl)]
      simp [cStep]
    | succ i ih =>
      intro k v
      show min (cStep c u (i + 1) k v) (cStep c u (i + 1) k (u (i + 1))) = _
      rw [ih, ih]
      have hU : insert v (sel u (i + 1)) = insert v (sel u i) ∪ insert (u (i + 1)) (sel u i) := by
        rw [hsel i]
        ext x
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      rw [inf'_eq _ _ _ ((Finset.insert_nonempty v (sel u i)).mono Finset.subset_union_left) _ hU]
      rw [Finset.inf'_union]
  have hcompl : ∀ j v, ((Jstep u j).erase v)ᶜ = insert v (sel u j) := by
    intro j v
    ext x
    simp only [Jstep, Finset.mem_compl, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_insert]
    tauto
  have hJ : ∀ j, Jstep u (j + 1) = (Jstep u j).erase (u (j + 1)) := by
    intro j
    ext x
    simp only [Jstep, hsel, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert]
    tauto
  have hz : ∀ j v, zStep c p u (j + 1) v =
      reductionCost c p ((Jstep u j).erase v) (compl_erase_nonempty _ _) := by
    intro j v
    simp only [zStep, reductionCost, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hkey j k v]
    congr 1
    exact inf'_eq _ _ _ _ _ (hcompl j v).symm
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨hmem, hle⟩ := hrun i hi
    refine ⟨hmem, fun v hv => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := (Finset.mem_Icc.1 hi).1; omega⟩
    have h1 := hle v hv
    simp only [Nat.add_sub_cancel] at h1 ⊢
    rw [hz, hz] at h1
    exact h1
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := (Finset.mem_Icc.1 hi).1; omega⟩
    rw [hz]
    exact rc_eq _ _ _ _ (hJ j).symm
