-- Prove2me | solution 1 for TSTutorial.KnownStandard.case_first_action_two
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:10:40.931877+00:00
-- url     : https://prove2.me/submissions/2c903e87-fc25-4206-82f7-ca2c89824062

import Definitions.Def_TSTutorial_KnownStandard_Setting

open TSTutorial.KnownStandard
open scoped BigOperators

private lemma reward_pos (θ : Bool) (a : Fin 2) (y : Bool) : 0 < rewardProb θ a y := by
  fin_cases a <;> cases θ <;> cases y <;> norm_num [rewardProb, succProb]

private lemma like_pos {T : ℕ} (θ : Bool) (h : Hist T) : 0 < like θ h := by
  exact Finset.prod_pos fun s _ => reward_pos θ (h s).1 (h s).2

private lemma post_bounds {T : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (h : Hist T) :
    0 < post p h ∧ post p h ≤ 1 := by
  have ha := mul_pos hp (like_pos true h)
  have hb := mul_nonneg (sub_nonneg.mpr hp1) (like_pos false h).le
  have hd : 0 < p * like true h + (1 - p) * like false h := by linarith
  exact ⟨div_pos ha hd, (div_le_one hd).mpr (by linarith)⟩

private lemma reward_zero (θ y : Bool) : rewardProb θ 0 y = 1 / 2 := by
  cases y <;> norm_num [rewardProb, succProb]

private lemma post_zero {T : ℕ} (p : ℝ) (h : Hist T) (hz : ∀ s, (h s).1 = 0) :
    post p h = p := by
  have hl (θ : Bool) : like θ h = (1 / 2 : ℝ) ^ T := by
    simp [like, hz, reward_zero]
  unfold post
  rw [hl, hl]
  have hn : (1 / 2 : ℝ) ^ T ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : p * (1 / 2 : ℝ) ^ T + (1 - p) * (1 / 2 : ℝ) ^ T = (1 / 2 : ℝ) ^ T := by ring
  rw [he, mul_div_cancel_right₀ _ hn]

private def Consistent (f : Strategy) (p : ℝ) {T : ℕ} (h : Hist T) : Prop :=
  ∀ s, (h s).1 = f (post p (histPrefix h s))

private lemma law_consistent (f : Strategy) (p : ℝ) (T : ℕ) (θ : Bool) (h : Hist T)
    (hn : lawGiven f p T θ h ≠ 0) : Consistent f p h := by
  intro s
  by_contra hs
  have he : lawGiven f p T θ h = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [act, hs]
  exact hn he

private lemma consistent_zero (f : Strategy) (p : ℝ) (hf : f p = 0)
    {T : ℕ} (h : Hist T) (hc : Consistent f p h) : ∀ s, (h s).1 = 0 := by
  have aux : ∀ k, ∀ hk : k < T, (h ⟨k, hk⟩).1 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hz : ∀ j : Fin k, (histPrefix h ⟨k, hk⟩ j).1 = 0 := by
        intro j
        exact ih j.val j.isLt (lt_trans j.isLt hk)
      have hp := post_zero p (histPrefix h ⟨k, hk⟩) hz
      simpa [hp, hf] using hc ⟨k, hk⟩
  intro s
  exact aux s.val s.isLt

private lemma zero_consistent (f : Strategy) (p : ℝ) (hf : f p = 0)
    {T : ℕ} (h : Hist T) (hz : ∀ s, (h s).1 = 0) : Consistent f p h := by
  intro s
  have hp := post_zero p (histPrefix h s) (fun j => hz (Fin.castLE s.isLt.le j))
  simpa [hp, hf] using hz s

private lemma one_policy (f : Strategy) (hf : ∀ p : ℝ, 0 < p → p ≤ 1 → f p = 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) {T : ℕ} (h : Hist T) (s : Fin T) :
    f (post p (histPrefix h s)) = 1 := by
  have hb := post_bounds p hp hp1 (histPrefix h s)
  exact hf _ hb.1 hb.2

private noncomputable def fixedKernel (θ : Bool) (a : Fin 2) (z : Fin 2 × Bool) : ℝ :=
  if z.1 = a then rewardProb θ a z.2 else 0

private lemma kernel_total (θ : Bool) (a : Fin 2) : ∑ z : Fin 2 × Bool, fixedKernel θ a z = 1 := by
  fin_cases a <;> cases θ <;> norm_num [fixedKernel, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fintype.sum_bool, rewardProb, succProb]

private lemma law_fixed (f : Strategy) (p : ℝ) (a : Fin 2)
    (he : ∀ {T : ℕ} (h : Hist T), Consistent f p h ↔ ∀ s, (h s).1 = a)
    (T : ℕ) (θ : Bool) (h : Hist T) :
    lawGiven f p T θ h = ∏ s, fixedKernel θ a (h s) := by
  classical
  by_cases ha : ∀ s, (h s).1 = a
  · have hc := (he h).mpr ha
    unfold lawGiven
    apply Finset.prod_congr rfl
    intro s hs
    have hact : act f p h s = 1 := if_pos (hc s)
    rw [hact, one_mul]
    simp [fixedKernel, ha s]
  · have hl : lawGiven f p T θ h = 0 := by
      by_contra hl
      exact ha ((he h).mp (law_consistent f p T θ h hl))
    rw [hl]
    symm
    push_neg at ha
    obtain ⟨s, hs⟩ := ha
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [fixedKernel, hs]

private lemma law_total (f : Strategy) (p : ℝ) (a : Fin 2)
    (he : ∀ {T : ℕ} (h : Hist T), Consistent f p h ↔ ∀ s, (h s).1 = a)
    (T : ℕ) (θ : Bool) : ∑ h : Hist T, lawGiven f p T θ h = 1 := by
  simp_rw [law_fixed f p a he]
  rw [← Fintype.prod_sum]
  simp [kernel_total]

private lemma regret_fixed (f : Strategy) (p : ℝ) (a : Fin 2)
    (he : ∀ {T : ℕ} (h : Hist T), Consistent f p h ↔ ∀ s, (h s).1 = a)
    (T : ℕ) :
    expRegret f p T = ∑ θ : Bool, prior p θ * (T * (optMean θ - succProb θ a)) := by
  unfold expRegret
  apply Finset.sum_congr rfl
  intro θ hθ
  congr 1
  calc
    _ = ∑ h : Hist T, lawGiven f p T θ h * (T * (optMean θ - succProb θ a)) := by
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hn : lawGiven f p T θ h = 0
      · simp [hn]
      · have ha := (he h).mp (law_consistent f p T θ h hn)
        simp only [ha, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by rw [← Finset.sum_mul, law_total f p a he]; simp

private lemma positive_history_consistent (f : Strategy) (p : ℝ) (T : ℕ) (h : Hist T)
    (hh : 0 < ∑ θ : Bool, prior p θ * lawGiven f p T θ h) : Consistent f p h := by
  by_contra hc
  have hz (θ : Bool) : lawGiven f p T θ h = 0 := by
    by_contra hz
    exact hc (law_consistent f p T θ h hz)
  simp [hz] at hh


theorem solution (f : Strategy) (hf : ∀ p : ℝ, 0 < p → p ≤ 1 → f p = 1)
    (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1) (T : ℕ) :
    (∀ h : Hist T, 0 < ∑ θ : Bool, prior p₀ θ * lawGiven f p₀ T θ h →
      ∀ s : Fin T, (h s).1 = 1) ∧
    expRegret f p₀ T = T * ((1 - p₀) / 4) := by
  have he : ∀ {t : ℕ} (h : Hist t), Consistent f p₀ h ↔ ∀ s, (h s).1 = 1 := by
    intro t h
    simp only [Consistent, one_policy f hf p₀ hp₀ hp₁]
  constructor
  · intro h hh
    exact (he h).mp (positive_history_consistent f p₀ T h hh)
  · rw [regret_fixed f p₀ 1 he T]
    norm_num [Fintype.sum_bool, prior, optMean, succProb]
    ring


