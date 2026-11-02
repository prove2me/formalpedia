-- Prove2me | solution 1 for RainbowEFX.Sublinear.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:47:01.769345+00:00
-- url     : https://prove2.me/submissions/bddecfa2-4dbc-4ddd-8174-4aa69598c557

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting
import Theorems.Thm_RainbowEFX_Sublinear_lemma_6
import Theorems.Thm_RainbowEFX_Sublinear_lemma_8
import Theorems.Thm_RainbowEFX_Sublinear_lemma_9
import Theorems.Thm_RainbowEFX_Sublinear_lemma_16
import Theorems.Thm_RainbowEFX_Sublinear_count_at_termination
import Theorems.Thm_RainbowEFX_Sublinear_choice_of_d

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ IsAlphaEFX (1 - ε) v X ∧
      ((pool X).card : ℝ) ≤ 64 * ((n : ℝ) / ε) ^ ((4 : ℝ) / 5) := by
  classical
  have hε1 : ε < 1 := by linarith
  -- strong Pareto domination strictly increases welfare
  have hPD : ∀ X' X : Fin n → Finset (Fin m), StronglyParetoDominates ε v X' X →
      welfare v X < welfare v X' := by
    intro X' X ⟨hle, i', hi'⟩
    unfold welfare
    apply Finset.sum_lt_sum (fun i _ => hle i) ⟨i', Finset.mem_univ _, ?_⟩
    have h0 : 0 ≤ v i' (X' i') := hv.2 _ _
    nlinarith
  have hmono : ∀ X' X : Fin n → Finset (Fin m), (∀ i, v i (X i) ≤ v i (X' i)) →
      welfare v X ≤ welfare v X' := by
    intro X' X h
    exact Finset.sum_le_sum (fun i _ => h i)
  set S : Finset (Fin n → Finset (Fin m)) :=
    Finset.univ.filter (fun X => IsPartialAllocation X ∧ IsAlphaEFX (1 - ε) v X) with hS
  have hS0 : (fun _ => (∅ : Finset (Fin m))) ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i j _ => Finset.disjoint_empty_left _, ?_⟩
    intro i j g hg
    simp at hg
  obtain ⟨X₀, hX₀S, hX₀max⟩ := Finset.exists_max_image S (welfare v) ⟨_, hS0⟩
  set T := S.filter (fun X => welfare v X = welfare v X₀) with hT
  obtain ⟨X, hXT, hXmin⟩ := Finset.exists_min_image T (fun X => (pool X).card) ⟨X₀, by
    simp [hT, hX₀S]⟩
  simp only [hT, Finset.mem_filter] at hXT
  obtain ⟨hXS, hXW⟩ := hXT
  have hXS' := hXS
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hXS'
  obtain ⟨hXP, hXE⟩ := hXS'
  -- make the envy graph acyclic (Lemma 6)
  obtain ⟨Y, hYP, hYE, hYv, hYac, hYpool⟩ : ∃ Y : Fin n → Finset (Fin m),
      IsPartialAllocation Y ∧ IsAlphaEFX (1 - ε) v Y ∧ (∀ i, v i (X i) ≤ v i (Y i)) ∧
      EnvyAcyclic v Y ∧ pool Y = pool X := by
    by_cases hc : ∃ i, Relation.TransGen (Envies v X) i i
    · exact lemma_6 v hv ε hε0 hε1 X hXP hXE hc
    · push_neg at hc
      exact ⟨X, hXP, hXE, fun i => le_rfl, hc, rfl⟩
  have hYS : Y ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hYP, hYE⟩
  have hYW : welfare v Y = welfare v X₀ :=
    le_antisymm (hX₀max Y hYS) (hXW ▸ hmono Y X hYv)
  -- maximality excludes any strongly Pareto-dominating (1-ε)-EFX allocation
  have hnoPD : ∀ X', IsPartialAllocation X' → IsAlphaEFX (1 - ε) v X' →
      ¬ StronglyParetoDominates ε v X' Y := by
    intro X' h1 h2 h3
    have hX'S : X' ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩
    have := hPD X' Y h3
    have := hX₀max X' hX'S
    linarith
  have hstar : Star ε v Y := by
    refine ⟨hYac, ?_, ?_⟩
    · rintro ⟨s, hs, g, hg, hno⟩
      obtain ⟨h1, h2, h3⟩ := lemma_8 v hv ε hε0 hε1 Y hYP hYE s hs g hg hno
      set Y' := Function.update Y s (insert g (Y s)) with hY'
      have hY'S : Y' ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩
      have hY'W : welfare v Y' = welfare v X₀ :=
        le_antisymm (hX₀max Y' hY'S) (hYW ▸ hmono Y' Y h3)
      have hY'T : Y' ∈ T := by simp [hT, hY'S, hY'W]
      have hmin := hXmin Y' hY'T
      have hsub : pool Y' ⊆ (pool Y).erase g := by
        intro x hx
        simp only [pool, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
          not_exists, not_and] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · rintro rfl
          apply hx s
          simp [hY']
        · simp only [pool, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
            not_exists, not_and]
          intro i hi
          apply hx i
          by_cases his : i = s
          · subst his; simp [hY', hi]
          · simp [hY', his, hi]
      have hc1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hg] at hc1
      have hpos : 0 < (pool Y).card := Finset.card_pos.mpr ⟨g, hg⟩
      rw [hYpool] at hc1 hpos
      omega
    · intro hU2
      obtain ⟨X', h1, h2, h3⟩ := lemma_9 v hv ε hε0 hε1 Y hYP hYE hU2
      exact hnoPD X' h1 h2 h3
  obtain ⟨⟨hd1, hd2, -⟩, hd3⟩ := choice_of_d n hn ε hε0 hε
  set d := ⌈((n : ℝ) / ε) ^ ((1 : ℝ) / 5)⌉₊ with hd
  refine ⟨Y, hYP, hYE, ?_⟩
  by_cases hL : d ^ 4 + d < (LX ε v Y d).card
  · obtain ⟨X', h1, h2, h3⟩ := lemma_16 hn v hv ε hε0 hε Y hYP hYE d hd1 hstar hL
    exact absurd h3 (hnoPD X' h1 h2)
  · push_neg at hL
    have hc := count_at_termination hn v hv ε hε0 hε Y hYP hYE d hd1 hstar hL
    rw [max_eq_right hd2] at hc
    linarith
