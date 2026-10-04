-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.determined_of_subgames
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:43:45.694535+00:00
-- url     : https://prove2.me/submissions/b48ad6ef-406d-4ca2-9cd0-0ca40b6c8919

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

set_option autoImplicit false

namespace P2MHelper7c9b5e65
open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree

/-- Saddle point in pure strategies with value `c`. -/
def Saddle (t : GameTree) : Prop :=
  ∃ (a : Strategy1 t) (b : Strategy2 t) (c : ℝ),
    (∀ y, c ≤ payoff t a y) ∧ (∀ x, payoff t x b ≤ c)

lemma v1_le_v2 (t : GameTree) : v1 t ≤ v2 t := by
  unfold v1 v2
  apply Finset.sup'_le
  intro x _
  apply Finset.le_inf'
  intro y _
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ y))
    (Finset.le_sup' (fun x => payoff t x y) (Finset.mem_univ x))

lemma det_of_saddle (t : GameTree) (h : Saddle t) : IsStrictlyDetermined t := by
  obtain ⟨a, b, c, ha, hb⟩ := h
  have h1 : c ≤ v1 t := by
    unfold v1
    exact Finset.le_sup'_of_le _ (Finset.mem_univ a) (Finset.le_inf' _ _ (fun y _ => ha y))
  have h2 : v2 t ≤ c := by
    unfold v2
    exact Finset.inf'_le_of_le _ (Finset.mem_univ b) (Finset.sup'_le _ _ (fun x _ => hb x))
  exact le_antisymm (v1_le_v2 t) (by linarith)

lemma saddle_of_det (t : GameTree) (h : IsStrictlyDetermined t) : Saddle t := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Strategy1 t))
    (fun τ₁ => Finset.univ.inf' Finset.univ_nonempty fun τ₂ : Strategy2 t => payoff t τ₁ τ₂)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Strategy2 t))
    (fun τ₂ => Finset.univ.sup' Finset.univ_nonempty fun τ₁ : Strategy1 t => payoff t τ₁ τ₂)
  refine ⟨a, b, v1 t, ?_, ?_⟩
  · intro y
    have : v1 t = _ := ha
    rw [this]
    exact Finset.inf'_le _ (Finset.mem_univ y)
  · intro x
    have h' : v1 t = v2 t := h
    rw [h']
    have : v2 t = _ := hb
    rw [this]
    exact Finset.le_sup' (fun x => payoff t x b) (Finset.mem_univ x)

lemma saddle_step (t : GameTree) (h : ∀ s ∈ t.firstMoveSubgames, Saddle s) : Saddle t := by
  cases t with
  | leaf w => exact ⟨(), (), w, fun _ => le_rfl, fun _ => le_rfl⟩
  | chance α p next hp hsum =>
    have hs : ∀ σ, ∃ (a : Strategy1 (next σ)) (b : Strategy2 (next σ)) (c : ℝ),
        (∀ y, c ≤ payoff (next σ) a y) ∧ (∀ x, payoff (next σ) x b ≤ c) :=
      fun σ => h _ (Set.mem_range_self σ)
    choose a b c ha hb using hs
    refine ⟨(fun σ => a σ : (σ : Fin α) → Strategy1 (next σ)),
      (fun σ => b σ : (σ : Fin α) → Strategy2 (next σ)), ∑ σ, p σ * c σ, ?_, ?_⟩
    · show ∀ y : ((σ : Fin α) → Strategy2 (next σ)),
        ∑ σ, p σ * c σ ≤ ∑ σ, p σ * payoff (next σ) (a σ) (y σ)
      intro y
      exact Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (ha σ (y σ)) (hp σ)
    · show ∀ x : ((σ : Fin α) → Strategy1 (next σ)),
        ∑ σ, p σ * payoff (next σ) (x σ) (b σ) ≤ ∑ σ, p σ * c σ
      intro x
      exact Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hb σ (x σ)) (hp σ)
  | move1 α hα next =>
    have hs : ∀ σ, ∃ (a : Strategy1 (next σ)) (b : Strategy2 (next σ)) (c : ℝ),
        (∀ y, c ≤ payoff (next σ) a y) ∧ (∀ x, payoff (next σ) x b ≤ c) :=
      fun σ => h _ (Set.mem_range_self σ)
    choose a b c ha hb using hs
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin α)) c
      ⟨⟨0, hα⟩, Finset.mem_univ _⟩
    refine ⟨((m, fun σ => a σ) : Fin α × ((σ : Fin α) → Strategy1 (next σ))),
      (fun σ => b σ : (σ : Fin α) → Strategy2 (next σ)), c m, ?_, ?_⟩
    · show ∀ y : ((σ : Fin α) → Strategy2 (next σ)), c m ≤ payoff (next m) (a m) (y m)
      intro y
      exact ha m (y m)
    · show ∀ x : Fin α × ((σ : Fin α) → Strategy1 (next σ)),
        payoff (next x.1) (x.2 x.1) (b x.1) ≤ c m
      intro x
      exact (hb x.1 (x.2 x.1)).trans (hm x.1 (Finset.mem_univ _))
  | move2 α hα next =>
    have hs : ∀ σ, ∃ (a : Strategy1 (next σ)) (b : Strategy2 (next σ)) (c : ℝ),
        (∀ y, c ≤ payoff (next σ) a y) ∧ (∀ x, payoff (next σ) x b ≤ c) :=
      fun σ => h _ (Set.mem_range_self σ)
    choose a b c ha hb using hs
    obtain ⟨m, -, hm⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin α)) c
      ⟨⟨0, hα⟩, Finset.mem_univ _⟩
    refine ⟨(fun σ => a σ : (σ : Fin α) → Strategy1 (next σ)),
      ((m, fun σ => b σ) : Fin α × ((σ : Fin α) → Strategy2 (next σ))), c m, ?_, ?_⟩
    · show ∀ y : Fin α × ((σ : Fin α) → Strategy2 (next σ)),
        c m ≤ payoff (next y.1) (a y.1) (y.2 y.1)
      intro y
      exact (hm y.1 (Finset.mem_univ _)).trans (ha y.1 (y.2 y.1))
    · show ∀ x : ((σ : Fin α) → Strategy1 (next σ)), payoff (next m) (x m) (b m) ≤ c m
      intro x
      exact hb m (x m)

end P2MHelper7c9b5e65

open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree in
theorem solution (t : GameTree)
    (h : ∀ s ∈ t.firstMoveSubgames, IsStrictlyDetermined s) :
    IsStrictlyDetermined t := by
  exact P2MHelper7c9b5e65.det_of_saddle t
    (P2MHelper7c9b5e65.saddle_step t fun s hs => P2MHelper7c9b5e65.saddle_of_det s (h s hs))
