-- Prove2me | solution 1 for SubscriptionPlanning.GrandOptimal.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:36:41.395865+00:00
-- url     : https://prove2.me/submissions/00167d0c-e5d8-4eb2-a604-c2973ddf4e0e

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

open MeasureTheory SubscriptionPlanning.GrandOptimal

namespace SubPlanL5Aux

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


theorem util_measurable (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (o : WithBot (Fin m)) : Measurable (fun ω => util M i S r ω o) := by
  induction o using WithBot.recBotCoe with
  | bot => simpa [util] using hM.measV0
  | coe j =>
    by_cases hj : j ∈ S
    · simpa [util, hj] using hM.measV i j
    · have := (hM.measV i j).sub_const (r j)
      simp only [util, WithBot.recBotCoe_coe, hj, if_false]
      exact this

theorem best_measurable (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) : Measurable (fun ω => best M i S r ω) := by
  have heq : (fun ω => best M i S r ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun o => fun ω => util M i S r ω o) := by
    funext ω
    simp [best, Finset.sup'_apply]
  rw [heq]
  exact Finset.measurable_sup' _ (fun o _ => util_measurable M hM i S r o)

theorem chosen_measurableSet (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (o : WithBot (Fin m)) : MeasurableSet {ω | IsChosen M i S r ω o} := by
  have h1 : MeasurableSet {ω | util M i S r ω o = best M i S r ω} :=
    measurableSet_eq_fun (util_measurable M hM i S r o) (best_measurable M hM i S r)
  have h2 : MeasurableSet {ω | ∀ o' < o, util M i S r ω o' < best M i S r ω} := by
    have : {ω | ∀ o' < o, util M i S r ω o' < best M i S r ω} =
        ⋂ o' ∈ (Finset.univ.filter (fun o' => o' < o)), {ω | util M i S r ω o' < best M i S r ω} := by
      ext ω; simp
    rw [this]
    refine Finset.measurableSet_biInter _ (fun o' _ => ?_)
    exact measurableSet_lt (util_measurable M hM i S r o') (best_measurable M hM i S r)
  exact h1.inter h2

theorem rentPaid_integrable (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : Integrable (fun ω => rentPaid M i S r ω) M.P := by
  have := hM.isProb
  have hmeas : Measurable (fun ω => rentPaid M i S r ω) := by
    unfold rentPaid
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    by_cases hj : j ∈ S
    · simp [hj]
    · simpa [hj] using chosen_measurableSet M hM i S r (j : WithBot (Fin m))
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∑ j, r j) (Filter.Eventually.of_forall ?_)
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (rentPaid_nonneg M i S r hr ω)]
  unfold rentPaid
  refine Finset.sum_le_sum (fun j _ => ?_)
  split_ifs
  · exact le_rfl
  · exact hr j

theorem rentPaid_mono (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hr : ∀ j, 0 ≤ r j) (ω : Ω) : rentPaid M i S r ω ≤ rentPaid M i ∅ r ω := by
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
    have hb := best_mono M i (Finset.empty_subset S) r hr ω
    have hu : util M i ∅ r ω (j : WithBot (Fin m)) = util M i S r ω (j : WithBot (Fin m)) := by
      simp [util, hjS]
    have hle : util M i ∅ r ω (j : WithBot (Fin m)) ≤ best M i ∅ r ω :=
      Finset.le_sup' (util M i ∅ r ω) (Finset.mem_univ _)
    have hc0 : IsChosen M i ∅ r ω (j : WithBot (Fin m)) := by
      refine ⟨?_, fun o' ho' => ?_⟩
      · have e1 := hjc.1
        exact le_antisymm hle (by linarith)
      · have h1 := hjc.2 o' ho'
        have h2 := util_mono M i (Finset.empty_subset S) r hr ω o'
        have h3 : best M i S r ω ≤ best M i ∅ r ω := by
          rw [← hjc.1, ← hu]; exact hle
        linarith
    rw [hrp]
    unfold rentPaid
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), if_pos ⟨Finset.notMem_empty j, hc0⟩]
    refine le_add_of_nonneg_left (Finset.sum_nonneg fun j' _ => ?_)
    split_ifs
    · exact hr j'
    · exact le_rfl
  · push Not at h
    have hrp : rentPaid M i S r ω = 0 := by
      unfold rentPaid
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg]
      rintro ⟨hjS, hjc⟩
      exact h j hjS hjc
    rw [hrp]
    exact rentPaid_nonneg M i ∅ r hr ω

end SubPlanL5Aux

open SubPlanL5Aux in
theorem solution {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : SubscriptionPlanning.GrandOptimal.Model n m Ω) (hM : M.Valid)
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (i : Fin n) (S : Finset (Fin m)) :
    SubscriptionPlanning.GrandOptimal.rent M i S r ≤ SubscriptionPlanning.GrandOptimal.rent M i ∅ r ∧
      SubscriptionPlanning.GrandOptimal.rent M i ∅ r ≤ SubscriptionPlanning.GrandOptimal.subGain M i Finset.univ r := by
  refine ⟨?_, ?_⟩
  · unfold rent
    exact integral_mono (rentPaid_integrable M hM i S r hr) (rentPaid_integrable M hM i ∅ r hr)
      (fun ω => rentPaid_mono M i S r hr ω)
  · have hint := rentPaid_integrable M hM i ∅ r hr
    have h1 : ∫ ω, (best M i ∅ r ω + rentPaid M i ∅ r ω) ∂M.P ≤
        ∫ ω, best M i Finset.univ r ω ∂M.P :=
      integral_mono ((best_integrable M hM i ∅ r).add hint) (best_integrable M hM i _ r)
        (fun ω => best_add_rentPaid M i ∅ r hr ω)
    rw [integral_add (best_integrable M hM i ∅ r) hint] at h1
    unfold rent subGain
    linarith
