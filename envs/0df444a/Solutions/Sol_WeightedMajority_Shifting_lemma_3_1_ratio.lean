-- Prove2me | solution 1 for WeightedMajority.Shifting.lemma_3_1_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:59:43.325482+00:00
-- url     : https://prove2.me/submissions/17cef841-ac04-48db-8d29-8c10b5aba722

import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML



namespace WeightedMajority.Shifting

open Finset

lemma wml_pos {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) : ∀ k, k ≤ T → ∀ i, 0 < w k i := by
  intro k
  induction k with
  | zero => intro _ i; exact hrun.init_pos i
  | succ k ih =>
    intro hk i
    have := hrun.update ⟨k, by omega⟩
    simp only at this
    rw [this]
    have h := ih (by omega) i
    unfold wmlUpdate
    split_ifs
    · positivity
    · exact h

lemma wml_total_nonneg {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) (k : ℕ) (hk : k ≤ T) : 0 ≤ totalWeight (w k) :=
  Finset.sum_nonneg (fun i _ => (wml_pos hβ0 hrun k hk i).le)

lemma ratio_core {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (hmis : lam t ≠ ρ t) :
    totalWeight (w ((t : ℕ) + 1)) ≤ uFactor β γ * totalWeight (w t) := by
  have hW : 0 ≤ totalWeight (w t) := wml_total_nonneg hβ0 hrun t (by omega)
  have hpred := hrun.predict t
  have hupd := hrun.update t
  generalize hl : lam t = l at *
  generalize hr : ρ t = r at *
  generalize ha : w t = a at *
  have hb : ∀ b : Bool, b = r ↔ ¬ b = l := by
    revert hmis; intro hmis; intro b; cases b <;> cases l <;> cases r <;> simp at hmis ⊢
  obtain ⟨h1, h2⟩ := hpred
  have hq : voteWeight a (x t) r ≤ voteWeight a (x t) l := by
    by_contra hc
    have hc := not_le.1 hc
    cases l <;> cases r
    · exact absurd rfl hmis
    · exact absurd (h2 hc) (by simp)
    · exact absurd (h1 hc) (by simp)
    · exact absurd rfl hmis
  have hsplit : voteWeight a (x t) l + voteWeight a (x t) r = totalWeight a := by
    unfold voteWeight totalWeight
    have : univ.filter (fun i => x t i = r) = univ.filter (fun i => ¬ x t i = l) :=
      Finset.filter_congr (fun i _ => hb _)
    rw [this]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  set W := totalWeight a with hWdef
  -- pointwise bound
  have hpt : ∀ i ∈ univ.filter (fun i => x t i = l),
      a i ≤ (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) + γ / n * W := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    have hxr : x t i ≠ r := by
      intro h; exact (hb _).1 h hi
    by_cases hc : (γ / (n : ℝ)) * W < a i
    · rw [if_pos ⟨hmis, hxr, hc⟩]
      have : 0 ≤ γ / n * W := by positivity
      linarith
    · rw [if_neg (fun h => hc h.2.2)]; push_neg at hc; linarith
  have hsum := Finset.sum_le_sum hpt
  have hn : 0 < n ∨ n = 0 := by omega
  have hcard : ∑ i ∈ univ.filter (fun i => x t i = l), (γ / n * W) ≤ γ * W := by
    rcases hn with hn | hn
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((univ.filter (fun i => x t i = l)).card : ℝ) ≤ n := by
        have := Finset.card_filter_le (univ : Finset (Fin n)) (fun i => x t i = l)
        simpa using this
      have hnr : (0:ℝ) < n := by exact_mod_cast hn
      have : 0 ≤ γ / n * W := by positivity
      calc _ ≤ (n:ℝ) * (γ / n * W) := mul_le_mul_of_nonneg_right hc this
        _ = γ * W := by field_simp
    · subst hn
      simp
      positivity
  rw [Finset.sum_add_distrib] at hsum
  have hite : ∑ i ∈ univ.filter (fun i => x t i = l),
      (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0)
      = ∑ i, (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hx : x t i = l
    · simp [hx]
    · have hxr : x t i = r := (hb _).2 hx
      simp [hxr]
  have hpt2 : ∀ i, wmlUpdate β γ a (x t) r l i = a i - (1 - β) *
      (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) := by
    intro i
    simp only [wmlUpdate, ← hWdef]
    split_ifs <;> ring
  have hnew : totalWeight (w ((t : ℕ) + 1)) = W - (1 - β) *
      ∑ i, (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) := by
    rw [hupd]
    unfold totalWeight
    simp only [hpt2]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
  rw [hnew]
  rw [hite] at hsum
  have hu : uFactor β γ = (1 + β) / 2 + (1 - β) * γ := rfl
  rw [hu]
  have h1β : 0 < 1 - β := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (show W / 2 - γ * W ≤ ∑ i, (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) by
    unfold voteWeight at hq hsplit; linarith) h1β.le]

end WeightedMajority.Shifting

open WeightedMajority.Shifting


theorem solution {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (hmis : lam t ≠ ρ t) :
    totalWeight (w ((t : ℕ) + 1)) ≤ uFactor β γ * totalWeight (w t) := by
  exact ratio_core hβ0 hβ1 hγ0 hγ1 x ρ w lam hrun t hmis
