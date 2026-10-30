-- Prove2me | solution 1 for SubscriptionPlanning.GrandOptimal.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:29:55.964878+00:00
-- url     : https://prove2.me/submissions/83225345-3171-44e0-9bb6-26a3a41deb4e

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

open MeasureTheory SubscriptionPlanning.GrandOptimal

namespace SubPlanLemma2Aux

variable {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem util_mono (M : Model n m Ω) (i : Fin n) {S S' : Finset (Fin m)} (h : S ⊆ S')
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (ω : Ω) (o : WithBot (Fin m)) :
    util M i S r ω o ≤ util M i S' r ω o := by
  induction o using WithBot.recBotCoe with
  | bot => simp [util]
  | coe j =>
    simp only [util, WithBot.recBotCoe_coe]
    by_cases hj : j ∈ S
    · simp [hj, h hj]
    · rw [if_neg hj]
      split_ifs
      · linarith [hr j]
      · exact le_rfl

theorem best_mono (M : Model n m Ω) (i : Fin n) {S S' : Finset (Fin m)} (h : S ⊆ S')
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (ω : Ω) :
    best M i S r ω ≤ best M i S' r ω := by
  unfold best
  refine Finset.sup'_le _ _ (fun o _ => ?_)
  exact le_trans (util_mono M i h r hr ω o) (Finset.le_sup' _ (Finset.mem_univ o))

theorem best_integrable (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) : Integrable (fun ω => best M i S r ω) M.P := by
  have := hM.isProb
  have heq : (fun ω => best M i S r ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun o => fun ω => util M i S r ω o) := by
    funext ω
    simp [best, Finset.sup'_apply]
  rw [heq]
  refine Finset.sup'_induction _ _ (p := fun f => Integrable f M.P) ?_ ?_
  · intro a ha b hb
    exact ha.sup hb
  · intro o _
    induction o using WithBot.recBotCoe with
    | bot => simpa [util] using hM.intV0
    | coe j =>
      by_cases hj : j ∈ S
      · simpa [util, hj] using hM.intV i j
      · have := (hM.intV i j).sub (integrable_const (r j))
        simp only [util, WithBot.recBotCoe_coe, hj, if_false]
        exact this

theorem chosen_unique (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) (ω : Ω)
    {o1 o2 : WithBot (Fin m)} (h1 : IsChosen M i S r ω o1) (h2 : IsChosen M i S r ω o2) :
    o1 = o2 := by
  rcases lt_trichotomy o1 o2 with h | h | h
  · have := h2.2 o1 h
    rw [h1.1] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := h1.2 o2 h
    rw [h2.1] at this
    exact absurd this (lt_irrefl _)

theorem rentPaid_nonneg (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hr : ∀ j, 0 ≤ r j) (ω : Ω) : 0 ≤ rentPaid M i S r ω := by
  unfold rentPaid
  refine Finset.sum_nonneg (fun j _ => ?_)
  split_ifs
  · exact hr j
  · exact le_rfl

theorem best_add_rentPaid (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hr : ∀ j, 0 ≤ r j) (ω : Ω) :
    best M i S r ω + rentPaid M i S r ω ≤ best M i Finset.univ r ω := by
  by_cases h : ∃ j : Fin m, j ∉ S ∧ IsChosen M i S r ω (j : WithBot (Fin m))
  · obtain ⟨j, hjS, hjc⟩ := h
    have hrp : rentPaid M i S r ω = r j := by
      unfold rentPaid
      rw [Finset.sum_eq_single j]
      · rw [if_pos ⟨hjS, hjc⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨_, hbc⟩
        exact hb (WithBot.coe_injective (chosen_unique M i S r ω hbc hjc))
      · intro h; exact absurd (Finset.mem_univ j) h
    have hbest : best M i S r ω = M.V i j ω - r j := by
      rw [← hjc.1]
      simp [util, hjS]
    have hu : M.V i j ω ≤ best M i Finset.univ r ω := by
      have := Finset.le_sup' (util M i Finset.univ r ω) (Finset.mem_univ (j : WithBot (Fin m)))
      unfold best
      refine le_trans (le_of_eq ?_) this
      simp [util]
    rw [hrp, hbest]
    linarith
  · push Not at h
    have hrp : rentPaid M i S r ω = 0 := by
      unfold rentPaid
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg]
      rintro ⟨hjS, hjc⟩
      exact h j hjS hjc
    rw [hrp, add_zero]
    exact best_mono M i (Finset.subset_univ S) r hr ω

end SubPlanLemma2Aux

open SubPlanLemma2Aux in
theorem solution {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : SubscriptionPlanning.GrandOptimal.Model n m Ω) (hM : M.Valid)
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (i : Fin n) (S : Finset (Fin m)) :
    SubscriptionPlanning.GrandOptimal.subGain M i S r + SubscriptionPlanning.GrandOptimal.rent M i S r ≤
      SubscriptionPlanning.GrandOptimal.subGain M i Finset.univ r := by
  have hSU : ∫ ω, best M i S r ω ∂M.P ≤ ∫ ω, best M i Finset.univ r ω ∂M.P :=
    integral_mono (best_integrable M hM i S r) (best_integrable M hM i _ r)
      (fun ω => best_mono M i (Finset.subset_univ S) r hr ω)
  unfold subGain rent
  by_cases hint : Integrable (fun ω => rentPaid M i S r ω) M.P
  · have h1 : ∫ ω, (best M i S r ω + rentPaid M i S r ω) ∂M.P ≤
        ∫ ω, best M i Finset.univ r ω ∂M.P :=
      integral_mono ((best_integrable M hM i S r).add hint) (best_integrable M hM i _ r)
        (fun ω => best_add_rentPaid M i S r hr ω)
    rw [integral_add (best_integrable M hM i S r) hint] at h1
    linarith
  · rw [integral_undef hint]
    linarith
