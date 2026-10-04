-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.strictly_determined_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:11:18.566296+00:00
-- url     : https://prove2.me/submissions/2db83a4d-eb6b-443e-855f-577b8e6cb63d

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values
import Definitions.Def_TheoryOfGames_PerfectInfo_backwardValue



namespace TheoryOfGames.PerfectInfo

open GameTree

theorem sd_lowerStrat (t : GameTree) :
    ∃ s1 : Strategy1 t, ∀ s2 : Strategy2 t, backwardValue t ≤ payoff t s1 s2 := by
  induction t with
  | leaf w => exact ⟨(), fun _ => le_refl _⟩
  | chance α p next hp hsum ih =>
    choose f hf using ih
    refine ⟨(f : (σ : Fin α) → Strategy1 (next σ)), fun s2 => ?_⟩
    show ∑ σ, p σ * backwardValue (next σ) ≤ ∑ σ, p σ * payoff (next σ) (f σ) (s2 σ)
    exact Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hf σ (s2 σ)) (hp σ)
  | move1 α hα next ih =>
    choose f hf using ih
    obtain ⟨σ0, -, h0⟩ := Finset.exists_mem_eq_sup' (⟨⟨0, hα⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin α)).Nonempty)
      (fun σ : Fin α => backwardValue (next σ))
    refine ⟨((σ0, f) : Fin α × ((σ : Fin α) → Strategy1 (next σ))), fun s2 => ?_⟩
    show Finset.univ.sup' _ (fun σ : Fin α => backwardValue (next σ)) ≤ payoff (next σ0) (f σ0) (s2 σ0)
    rw [h0]; exact hf σ0 (s2 σ0)
  | move2 α hα next ih =>
    choose f hf using ih
    refine ⟨(f : (σ : Fin α) → Strategy1 (next σ)), fun s2 => ?_⟩
    show Finset.univ.inf' _ (fun σ : Fin α => backwardValue (next σ)) ≤ payoff (next s2.1) (f s2.1) (s2.2 s2.1)
    exact (Finset.inf'_le _ (Finset.mem_univ s2.1)).trans (hf s2.1 (s2.2 s2.1))

theorem sd_upperStrat (t : GameTree) :
    ∃ s2 : Strategy2 t, ∀ s1 : Strategy1 t, payoff t s1 s2 ≤ backwardValue t := by
  induction t with
  | leaf w => exact ⟨(), fun _ => le_refl _⟩
  | chance α p next hp hsum ih =>
    choose f hf using ih
    refine ⟨(f : (σ : Fin α) → Strategy2 (next σ)), fun s1 => ?_⟩
    show ∑ σ, p σ * payoff (next σ) (s1 σ) (f σ) ≤ ∑ σ, p σ * backwardValue (next σ)
    exact Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hf σ (s1 σ)) (hp σ)
  | move2 α hα next ih =>
    choose f hf using ih
    obtain ⟨σ0, -, h0⟩ := Finset.exists_mem_eq_inf' (⟨⟨0, hα⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin α)).Nonempty)
      (fun σ : Fin α => backwardValue (next σ))
    refine ⟨((σ0, f) : Fin α × ((σ : Fin α) → Strategy2 (next σ))), fun s1 => ?_⟩
    show payoff (next σ0) (s1 σ0) (f σ0) ≤ Finset.univ.inf' _ (fun σ : Fin α => backwardValue (next σ))
    rw [h0]; exact hf σ0 (s1 σ0)
  | move1 α hα next ih =>
    choose f hf using ih
    refine ⟨(f : (σ : Fin α) → Strategy2 (next σ)), fun s1 => ?_⟩
    show payoff (next s1.1) (s1.2 s1.1) (f s1.1) ≤ Finset.univ.sup' _ (fun σ : Fin α => backwardValue (next σ))
    exact (hf s1.1 (s1.2 s1.1)).trans (Finset.le_sup' (fun σ : Fin α => backwardValue (next σ)) (Finset.mem_univ s1.1))

theorem sd_core (t : GameTree) :
    v1 t = backwardValue t ∧ v2 t = backwardValue t := by
  obtain ⟨a, ha⟩ := sd_lowerStrat t
  obtain ⟨b, hb⟩ := sd_upperStrat t
  have h1 : backwardValue t ≤ v1 t := by
    unfold v1
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ a))
    exact Finset.le_inf' _ _ fun s2 _ => ha s2
  have h2 : v1 t ≤ backwardValue t := by
    unfold v1
    refine Finset.sup'_le _ _ fun s1 _ => ?_
    exact (Finset.inf'_le _ (Finset.mem_univ b)).trans (hb s1)
  have h3 : v2 t ≤ backwardValue t := by
    unfold v2
    refine (Finset.inf'_le _ (Finset.mem_univ b)).trans ?_
    exact Finset.sup'_le _ _ fun s1 _ => hb s1
  have h4 : backwardValue t ≤ v2 t := by
    unfold v2
    refine Finset.le_inf' _ _ fun s2 _ => ?_
    exact (ha s2).trans (Finset.le_sup' (fun s1 => payoff t s1 s2) (Finset.mem_univ a))
  exact ⟨le_antisymm h2 h1, le_antisymm h3 h4⟩

end TheoryOfGames.PerfectInfo

open TheoryOfGames.PerfectInfo
open GameTree

theorem solution (t : GameTree) :
    v1 t = backwardValue t ∧ v2 t = backwardValue t := by
  exact sd_core t
