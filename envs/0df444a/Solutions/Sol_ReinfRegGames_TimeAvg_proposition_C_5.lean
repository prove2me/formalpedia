-- Prove2me | solution 1 for ReinfRegGames.TimeAvg.proposition_C_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:34:42.754615+00:00
-- url     : https://prove2.me/submissions/a18b111a-b989-4561-9e79-8688ee4d036f

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
set_option autoImplicit false

lemma zzb_conj_ge {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ)
    (hc : ContinuousOn h (stdSimplex ℝ B)) (y x' : B → ℝ) (hx' : x' ∈ stdSimplex ℝ B) :
    y ⬝ᵥ x' - h x' ≤ ReinfRegGames.Extinction.conj h y := by
  unfold ReinfRegGames.Extinction.conj
  apply le_csSup
  · have hcont : ContinuousOn (fun x : B → ℝ => y ⬝ᵥ x - h x) (stdSimplex ℝ B) := by
      apply ContinuousOn.sub
      · apply Continuous.continuousOn
        unfold dotProduct
        fun_prop
      · exact hc
    exact (isCompact_stdSimplex ℝ B).bddAbove_image hcont
  · exact ⟨x', hx', rfl⟩

lemma zzb_pair {B : Type*} [Fintype B] [DecidableEq B]
    (h : (B → ℝ) → ℝ) (hc : ContinuousOn h (stdSimplex ℝ B))
    (p : B → ℝ) (hp : ∀ α, 0 ≤ p α) (hp1 : ∑ α, p α = 1) (hint : ∀ α, 0 < p α)
    {J : Type*} (y : J → B → ℝ)
    (hF : ∃ M : ℝ, ∀ j, |ReinfRegGames.Extinction.fenchelCoupling h p (y j)| ≤ M)
    (a b : B) (hab : a ≠ b) : ∃ M' : ℝ, ∀ j, y j a - y j b ≤ M' := by
  obtain ⟨M, hM⟩ := hF
  set x' : B → ℝ := fun i => p i + (if i = a then p b else 0) - (if i = b then p b else 0) with hx'
  have hx's : x' ∈ stdSimplex ℝ B := by
    constructor
    · intro i
      simp only [hx']
      by_cases hia : i = a
      · subst hia
        have : i ≠ b := hab
        simp [this]
        have := hp i; have := hint b; linarith
      · by_cases hib : i = b
        · subst hib; simp [hia]
        · simp [hia, hib]; exact hp i
    · simp only [hx', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hp1]
      ring
  have hdot : ∀ j, y j ⬝ᵥ x' = y j ⬝ᵥ p + y j a * p b - y j b * p b := by
    intro j
    simp only [hx', dotProduct, mul_add, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hb := hint b
  refine ⟨(M + h x' - h p) / p b, fun j => ?_⟩
  have h1 := zzb_conj_ge h hc (y j) x' hx's
  have h2 := (abs_le.mp (hM j)).2
  unfold ReinfRegGames.Extinction.fenchelCoupling at h2
  rw [hdot j] at h1
  rw [le_div_iff₀ hb]
  nlinarith

theorem solution {B : Type*} [Fintype B] [DecidableEq B]
    (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : AGT.IsLottery p) (hint : ∀ α, 0 < p α)
    {J : Type*} (y : J → B → ℝ) (hF : ∃ M : ℝ, ∀ j, |ReinfRegGames.Extinction.fenchelCoupling h p (y j)| ≤ M) :
    ∀ α β : B, ∃ M' : ℝ, ∀ j, |y j α - y j β| ≤ M' := by
  intro α β
  by_cases hab : α = β
  · subst hab; exact ⟨0, fun j => by simp⟩
  · obtain ⟨M1, h1⟩ := zzb_pair h hpen.1 p hp.1 hp.2 hint y hF α β hab
    obtain ⟨M2, h2⟩ := zzb_pair h hpen.1 p hp.1 hp.2 hint y hF β α (Ne.symm hab)
    refine ⟨max M1 M2, fun j => ?_⟩
    rw [abs_le]
    have a1 := h1 j; have a2 := h2 j
    constructor
    · have := le_max_right M1 M2; linarith
    · have := le_max_left M1 M2; linarith
