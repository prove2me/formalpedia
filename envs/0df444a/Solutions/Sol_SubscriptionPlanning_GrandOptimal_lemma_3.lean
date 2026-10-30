-- Prove2me | solution 1 for SubscriptionPlanning.GrandOptimal.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:35:24.174353+00:00
-- url     : https://prove2.me/submissions/44012be3-133a-4346-9255-fc104efa4eba

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

open MeasureTheory SubscriptionPlanning.GrandOptimal

namespace SubPlanL3Aux

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

theorem subGain_nonneg (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : 0 ≤ subGain M i S r := by
  unfold subGain
  have := integral_mono (best_integrable M hM i ∅ r) (best_integrable M hM i S r)
    (fun ω => best_mono M i (Finset.empty_subset S) r hr ω)
  linarith

theorem subGain_le (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : subGain M i S r ≤ subGain M i Finset.univ r := by
  unfold subGain
  have := integral_mono (best_integrable M hM i S r) (best_integrable M hM i Finset.univ r)
    (fun ω => best_mono M i (Finset.subset_univ S) r hr ω)
  linarith

theorem rent_nonneg (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hr : ∀ j, 0 ≤ r j) : 0 ≤ rent M i S r := by
  unfold rent
  refine integral_nonneg (fun ω => ?_)
  unfold rentPaid
  refine Finset.sum_nonneg (fun j _ => ?_)
  split_ifs
  · exact hr j
  · exact le_rfl

theorem subGain_empty (M : Model n m Ω) (i : Fin n) (r : Fin m → ℝ) : subGain M i ∅ r = 0 := by
  unfold subGain; ring


theorem relGain_facts (M : Model n m Ω) (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hC : Condition2 M r) (i j : Fin n) (S : Finset (Fin m)) :
    M.lam i * M.T * subGain M i Finset.univ r * relGain M j S r ≤ M.lam i * M.T * subGain M i S r := by
  have hlT : 0 < M.lam i * M.T := mul_pos (hM.lam_pos i) hM.T_pos
  unfold relGain
  rcases (subGain_nonneg M hM j Finset.univ r hr).lt_or_eq with hpos | hzero
  · have hc := hC.2 i j S
    have : subGain M i Finset.univ r * (subGain M j S r / subGain M j Finset.univ r) = subGain M i S r := by
      rw [mul_div_assoc', div_eq_iff hpos.ne']
      linarith
    rw [mul_assoc, this]
  · rw [← hzero, div_zero, mul_zero]
    exact mul_nonneg hlT.le (subGain_nonneg M hM i S r hr)

theorem relGain_self (M : Model n m Ω) (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (i : Fin n) (S : Finset (Fin m)) :
    M.lam i * M.T * subGain M i Finset.univ r * relGain M i S r = M.lam i * M.T * subGain M i S r := by
  unfold relGain
  rcases (subGain_nonneg M hM i Finset.univ r hr).lt_or_eq with hpos | hzero
  · have hne := hpos.ne'
    field_simp
  · have : subGain M i S r = 0 :=
      le_antisymm (by rw [hzero]; exact subGain_le M hM i S r hr) (subGain_nonneg M hM i S r hr)
    rw [this, ← hzero]; simp

theorem claim1 (M : Model n m Ω) (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hC : Condition2 M r) (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m))
    (hF : IsFeasible M r p S) (i i' : Fin n) (hg : relGain M i' (S i') r ≤ relGain M i (S i) r) :
    p (S i') ≤ p (S i) := by
  have h1 := hF.2 i' (S i)
  have h2 := relGain_facts M hM r hr hC i' i (S i)
  have h3 := relGain_self M hM r hr i' (S i')
  have hA : 0 ≤ M.lam i' * M.T * subGain M i' Finset.univ r :=
    mul_nonneg (mul_pos (hM.lam_pos i') hM.T_pos).le (subGain_nonneg M hM i' _ r hr)
  have h4 := mul_le_mul_of_nonneg_left hg hA
  linarith

end SubPlanL3Aux

open SubPlanL3Aux in
theorem solution {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : SubscriptionPlanning.GrandOptimal.Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (hC : SubscriptionPlanning.GrandOptimal.Condition2 M r)
    (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)) (hF : SubscriptionPlanning.GrandOptimal.IsFeasible M r p S)
    (i i' : Fin n)
    (hlt : M.lam i' * SubscriptionPlanning.GrandOptimal.subGain M i' Finset.univ r <
      M.lam i * SubscriptionPlanning.GrandOptimal.subGain M i Finset.univ r) :
    SubscriptionPlanning.GrandOptimal.relGain M i' (S i') r ≤ SubscriptionPlanning.GrandOptimal.relGain M i (S i) r ∧
      p (S i') ≤ p (S i) := by
  have hg : relGain M i' (S i') r ≤ relGain M i (S i) r := by
    by_contra hcon
    push Not at hcon
    have e1 := hF.2 i (S i')
    have e2 := hF.2 i' (S i)
    have f1 := relGain_facts M hM r hr hC i i' (S i')
    have f2 := relGain_facts M hM r hr hC i' i (S i)
    have g1 := relGain_self M hM r hr i (S i)
    have g2 := relGain_self M hM r hr i' (S i')
    have hT := hM.T_pos
    have hAlt : M.lam i' * M.T * subGain M i' Finset.univ r < M.lam i * M.T * subGain M i Finset.univ r := by
      have := mul_lt_mul_of_pos_right hlt hT
      linarith
    have : 0 < (M.lam i * M.T * subGain M i Finset.univ r - M.lam i' * M.T * subGain M i' Finset.univ r) *
        (relGain M i' (S i') r - relGain M i (S i) r) := mul_pos (by linarith) (by linarith)
    nlinarith
  exact ⟨hg, claim1 M hM r hr hC p S hF i i' hg⟩
