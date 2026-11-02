-- Prove2me | solution 1 for RainbowEFX.Sublinear.observation_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:49:47.263712+00:00
-- url     : https://prove2.me/submissions/a76b5cee-14eb-40b5-a430-f738db704d32

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hd : 1 ≤ d) (hstar : Star ε v X) :
    ((HX ε v X d).card : ℝ) < 2 * n / (ε * d) := by
  classical
  have mono : ∀ i (A B : Finset (Fin m)), A ⊆ B → v i A ≤ v i B := by
    intro i A B hAB
    rw [hv.1 i A, hv.1 i B]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hv.2 i {x})
  -- each agent finds fewer than 2/ε unallocated goods valuable
  have hagent : ∀ i, (((pool X).filter (fun g => Valuable ε v X g i)).card : ℝ) * ε < 2 := by
    intro i
    set V := (pool X).filter (fun g => Valuable ε v X g i) with hV
    have hU2 : ¬ HeavilyEnvies ε v X i (pool X) := fun h => hstar.2.2 ⟨i, h⟩
    simp only [HeavilyEnvies, not_lt] at hU2
    set x := v i (X i)
    have hx0 : 0 ≤ x := hv.2 _ _
    have hP0 : 0 ≤ v i (pool X) := hv.2 _ _
    have hP : v i (pool X) ≤ 2 * x := by nlinarith
    have hVP : v i V ≤ v i (pool X) := mono i _ _ (Finset.filter_subset _ _)
    rcases V.eq_empty_or_nonempty with hVe | hVne
    · rw [hVe]; simp
    · have hsum : ∑ g ∈ V, ε * x < ∑ g ∈ V, v i {g} := by
        apply Finset.sum_lt_sum_of_nonempty hVne
        intro g hg
        rw [hV, Finset.mem_filter] at hg
        exact hg.2
      rw [Finset.sum_const, nsmul_eq_mul, ← hv.1 i V] at hsum
      have hlt : (V.card : ℝ) * ε * x < 2 * x := by nlinarith
      have hxpos : 0 < x := by
        rcases hx0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hlt; simp at hlt
      nlinarith
  -- double counting
  have hdc : ∑ g ∈ HX ε v X d, (valuableAgents ε v X g).card =
      ∑ i, ((HX ε v X d).filter (fun g => Valuable ε v X g i)).card := by
    simp only [valuableAgents, Finset.card_filter]
    exact Finset.sum_comm
  have hlow : (HX ε v X d).card * (d + 1) ≤ ∑ g ∈ HX ε v X d, (valuableAgents ε v X g).card := by
    have : (HX ε v X d).card * (d + 1) = ∑ _g ∈ HX ε v X d, (d + 1) := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [this]
    apply Finset.sum_le_sum
    intro g hg
    simp only [HX, Finset.mem_filter] at hg
    exact hg.2
  have hup : ∀ i, ((HX ε v X d).filter (fun g => Valuable ε v X g i)).card ≤
      ((pool X).filter (fun g => Valuable ε v X g i)).card := by
    intro i
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    exact Finset.filter_subset _ _
  have hnat : (HX ε v X d).card * (d + 1) ≤
      ∑ i, ((pool X).filter (fun g => Valuable ε v X g i)).card := by
    calc (HX ε v X d).card * (d + 1) ≤ ∑ g ∈ HX ε v X d, (valuableAgents ε v X g).card := hlow
      _ = _ := hdc
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hup i)
  have hreal : ((HX ε v X d).card : ℝ) * (d + 1) ≤
      ∑ i, (((pool X).filter (fun g => Valuable ε v X g i)).card : ℝ) := by
    exact_mod_cast hnat
  have hsumlt : (∑ i, (((pool X).filter (fun g => Valuable ε v X g i)).card : ℝ)) * ε <
      2 * n := by
    rw [Finset.sum_mul]
    have : ∑ i : Fin n, (((pool X).filter (fun g => Valuable ε v X g i)).card : ℝ) * ε <
        ∑ _i : Fin n, (2 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
      · intro i _; exact hagent i
    simpa [mul_comm] using this
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [lt_div_iff₀ (by positivity)]
  have hH0 : (0 : ℝ) ≤ (HX ε v X d).card := by positivity
  nlinarith
