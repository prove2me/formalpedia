-- Prove2me | solution 1 for SampleCRS.AlmostGreedy.Supplement.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T14:14:05.720184+00:00
-- url     : https://prove2.me/submissions/99009ddd-db08-4fce-be6f-d52c3d5117e9

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

open SampleCRS.AlmostGreedy SampleCRS.AlmostGreedy.Supplement CommitteeVoting.SingleVoter

namespace L31Aux

lemma foldl_stuck {α : Type*} (f : Finset α → α → Finset α)
    (hstuck : ∀ A a, A.card ≠ 0 → f A a = A) :
    ∀ (l : List α) (A : Finset α), A.card ≠ 0 → l.foldl f A = A := by
  intro l
  induction l with
  | nil => intro A _; rfl
  | cons a l ih => intro A hA; rw [List.foldl_cons, hstuck A a hA, ih A hA]

lemma foldl_char {α : Type*} [LinearOrder α] (c : α → Prop) (f : Finset α → α → Finset α)
    (hstuck : ∀ A a, A.card ≠ 0 → f A a = A) (hyes : ∀ a, c a → f ∅ a = {a})
    (hno : ∀ a, ¬ c a → f ∅ a = ∅) :
    ∀ (l : List α), l.Pairwise (· < ·) → ∀ x,
      x ∈ l.foldl f ∅ ↔ x ∈ l ∧ c x ∧ ∀ y ∈ l, y < x → ¬ c y := by
  intro l
  induction l with
  | nil => intro _ x; simp
  | cons a l ih =>
    intro hl x
    rw [List.pairwise_cons] at hl
    rw [List.foldl_cons]
    by_cases ha : c a
    · rw [hyes a ha, foldl_stuck f hstuck l {a} (by simp)]
      simp only [Finset.mem_singleton, List.mem_cons]
      constructor
      · rintro rfl
        refine ⟨Or.inl rfl, ha, fun y hy hya => ?_⟩
        rcases hy with rfl | hy
        · exact absurd hya (lt_irrefl _)
        · exact absurd (hl.1 y hy) (not_lt.mpr hya.le)
      · rintro ⟨hx, hcx, hmin⟩
        rcases hx with rfl | hx
        · rfl
        · exact absurd ha (hmin a (Or.inl rfl) (hl.1 x hx))
    · rw [hno a ha, ih hl.2 x]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨hx, hcx, hmin⟩
        refine ⟨Or.inr hx, hcx, fun y hy hyx => ?_⟩
        rcases hy with rfl | hy
        · exact ha
        · exact hmin y hy hyx
      · rintro ⟨hx, hcx, hmin⟩
        rcases hx with rfl | hx
        · exact absurd hcx ha
        · exact ⟨hx, hcx, fun y hy hyx => hmin y (Or.inr hy) hyx⟩

lemma mem_run {n : ℕ} (t : Threshold n) (X : Fin n → Bool) (i : Fin n) :
    i ∈ thresholdRun t X ↔ (afterThreshold t i ∧ X i = true) ∧
      ∀ j, j < i → ¬ (afterThreshold t j ∧ X j = true) := by
  unfold thresholdRun
  refine (foldl_char (fun a => afterThreshold t a ∧ X a = true) _ ?_ ?_ ?_ _ ?_ i).trans ?_
  · intro A a hA
    rw [if_neg (fun h => hA h.1)]
  · intro a ha
    rw [if_pos ⟨Finset.card_empty, ha⟩]
    simp
  · intro a ha
    rw [if_neg (fun h => ha h.2)]
  · exact List.pairwise_ofFn.mpr (fun a b h => h)
  · constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨h1, fun j hj => h2 j (by simp) hj⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simp, h1, fun y _ hy => h2 y hy⟩

lemma sampleSet_sum {n : ℕ} (F : Finset (Fin n) → ℝ) :
    ∑ Y : Fin n → Bool, F (sampleSet Y) = ∑ A : Finset (Fin n), F A := by
  let e : (Fin n → Bool) ≃ Finset (Fin n) :=
    { toFun := fun Y => sampleSet Y
      invFun := fun A k => decide (k ∈ A)
      left_inv := by
        intro Y
        funext k
        simp [sampleSet]
      right_inv := by
        intro A
        ext k
        simp [sampleSet] }
  exact Fintype.sum_equiv e _ _ (fun Y => rfl)

lemma activationWeight_eq {n : ℕ} (p : Fin n → ℝ) (Y : Fin n → Bool) :
    activationWeight p Y = pbWeight p Finset.univ (sampleSet Y) := by
  unfold activationWeight
  congr 1

lemma sum_pattern {n : ℕ} (p : Fin n → ℝ) (T J : Finset (Fin n)) (hTJ : Disjoint T J) :
    ∑ A : Finset (Fin n), (if T ⊆ A ∧ Disjoint J A then pbWeight p Finset.univ A else 0)
      = (∏ k ∈ T, p k) * ∏ k ∈ J, (1 - p k) := by
  have h := Finset.prod_add (fun k => if k ∈ J then (0:ℝ) else p k)
    (fun k => if k ∈ T then (0:ℝ) else 1 - p k) (Finset.univ : Finset (Fin n))
  rw [Finset.powerset_univ] at h
  have hl : ∏ k : Fin n, ((if k ∈ J then (0:ℝ) else p k) + if k ∈ T then (0:ℝ) else 1 - p k)
      = (∏ k ∈ T, p k) * ∏ k ∈ J, (1 - p k) := by
    calc _ = ∏ k : Fin n, ((if k ∈ T then p k else 1) * (if k ∈ J then 1 - p k else 1)) := by
          apply Finset.prod_congr rfl
          intro k _
          by_cases hT : k ∈ T
          · have hJ : k ∉ J := Finset.disjoint_left.mp hTJ hT
            simp [hT, hJ]
          · by_cases hJ : k ∈ J <;> simp [hT, hJ]
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter,
            Finset.univ_inter]
  rw [← hl, h]
  apply Finset.sum_congr rfl
  intro A _
  unfold pbWeight
  by_cases hc : T ⊆ A ∧ Disjoint J A
  · rw [if_pos hc]
    congr 1
    · apply Finset.prod_congr rfl
      intro a ha
      rw [if_neg (Finset.disjoint_right.mp hc.2 ha)]
    · apply Finset.prod_congr rfl
      intro a ha
      have : a ∉ T := fun haT => (Finset.mem_sdiff.mp ha).2 (hc.1 haT)
      rw [if_neg this]
  · rw [if_neg hc]
    rcases not_and_or.mp hc with h1 | h1
    · obtain ⟨a, haT, haA⟩ := Finset.not_subset.mp h1
      have : ∏ a ∈ Finset.univ \ A, (if a ∈ T then (0:ℝ) else 1 - p a) = 0 :=
        Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haA⟩) (if_pos haT)
      rw [this, mul_zero]
    · rw [Finset.not_disjoint_iff] at h1
      obtain ⟨a, haJ, haA⟩ := h1
      have : ∏ a ∈ A, (if a ∈ J then (0:ℝ) else p a) = 0 :=
        Finset.prod_eq_zero haA (if_pos haJ)
      rw [this, zero_mul]

lemma tel {n : ℕ} (q : Fin n → ℝ) (s : Finset (Fin n)) :
    ∏ j ∈ s, (1 - q j) + ∑ k ∈ s, q k * ∏ j ∈ s.filter (fun j => k < j), (1 - q j) = 1 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h1 : (insert a s).filter (fun j => a < j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j hj hlt
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact lt_irrefl _ hlt
      · exact lt_asymm hlt (ha j hj)
    have h2 : ∀ k ∈ s, ∏ j ∈ (insert a s).filter (fun j => k < j), (1 - q j)
        = (1 - q a) * ∏ j ∈ s.filter (fun j => k < j), (1 - q j) := by
      intro k hk
      rw [Finset.filter_insert, if_pos (ha k hk),
        Finset.prod_insert (fun h => has (Finset.mem_filter.mp h).1)]
    rw [h1, Finset.prod_empty, Finset.sum_congr rfl (fun k hk => by rw [h2 k hk])]
    have h3 : ∑ k ∈ s, q k * ((1 - q a) * ∏ j ∈ s.filter (fun j => k < j), (1 - q j))
        = (1 - q a) * ∑ k ∈ s, q k * ∏ j ∈ s.filter (fun j => k < j), (1 - q j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [h3]
    linear_combination (1 - q a) * ih

end L31Aux

open L31Aux in
theorem solution {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1)
    (w : Threshold n → ℝ) (hzero : w none = (1 / 2 : ℝ))
    (hatoms : ∀ i : Fin n, w (some i) = p i / 2) :
    ThresholdFeasible n ∧ ∀ i, 0 < p i → (1 / 2 : ℝ) ≤ thresholdC p w i := by
  constructor
  · intro t X
    refine ⟨Finset.card_le_one.mpr (fun a ha b hb => ?_),
      fun i hi => ((mem_run t X i).mp hi).1.2⟩
    rw [mem_run] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd ha.1 (hb.2 a h)
    · exact h
    · exact absurd hb.1 (ha.2 b h)
  · intro i hpi
    classical
    have hE : ∀ t, activationE p (fun X => if i ∈ thresholdRun t X then (1:ℝ) else 0)
        = p i * g p i t := by
      intro t
      unfold g
      split_ifs with hti
      · rw [← Finset.prod_singleton p i, ← sum_pattern p {i} _ ?_]
        · unfold activationE
          rw [← sampleSet_sum]
          apply Finset.sum_congr rfl
          intro X _
          rw [activationWeight_eq]
          dsimp only
          by_cases hm : i ∈ thresholdRun t X
          · rw [if_pos hm, mul_one, if_pos]
            rw [mem_run] at hm
            refine ⟨?_, ?_⟩
            · simp [sampleSet, hm.1.2]
            · rw [Finset.disjoint_left]
              intro j hj hjX
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              simp only [sampleSet, Finset.mem_filter, Finset.mem_univ, true_and] at hjX
              exact hm.2 j hj.2 ⟨hj.1, hjX⟩
          · rw [if_neg hm, mul_zero, if_neg]
            rintro ⟨h1, h2⟩
            apply hm
            rw [mem_run]
            refine ⟨⟨hti, ?_⟩, fun j hj hc => ?_⟩
            · simpa [sampleSet] using h1
            · have := Finset.disjoint_left.mp h2
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc.1, hj⟩)
              exact this (by simp [sampleSet, hc.2])
        · rw [Finset.disjoint_singleton_left]
          intro h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact lt_irrefl i h.2
      · rw [mul_zero]
        unfold activationE
        apply Finset.sum_eq_zero
        intro X _
        dsimp only
        rw [if_neg (fun hm => hti ((mem_run t X i).mp hm).1.1), mul_zero]
    unfold thresholdC
    simp only [hE]
    have hfac : ∑ t, w t * (p i * g p i t) = p i * ∑ t, w t * g p i t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hfac, mul_div_cancel_left₀ _ hpi.ne', Fintype.sum_option, hzero]
    simp only [hatoms]
    have hg0 : g p i none = ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - p j) := by
      unfold g
      simp [afterThreshold]
    have hgk : ∀ k, g p i (some k) = if k < i then
        ∏ j ∈ (Finset.univ.filter (fun j => j < i)).filter (fun j => k < j), (1 - p j)
        else 0 := by
      intro k
      unfold g
      by_cases hk : k < i
      · rw [if_pos (show afterThreshold (some k) i from hk), if_pos hk]
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show (k < j ∧ j < i) ↔ (j < i ∧ k < j)
        exact and_comm
      · rw [if_neg (show ¬ afterThreshold (some k) i from hk), if_neg hk]
    have hsum : ∑ k, p k / 2 * g p i (some k) = (1 / 2) *
        ∑ k ∈ Finset.univ.filter (fun j => j < i),
          p k * ∏ j ∈ (Finset.univ.filter (fun j => j < i)).filter (fun j => k < j), (1 - p j) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hgk k]
      split_ifs <;> ring
    rw [hsum, hg0]
    have htel := tel p (Finset.univ.filter (fun j => j < i))
    linarith
