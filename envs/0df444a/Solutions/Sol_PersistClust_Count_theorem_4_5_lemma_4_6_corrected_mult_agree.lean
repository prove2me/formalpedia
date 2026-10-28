-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_lemma_4_6_corrected_mult_agree
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:14:18.077774+00:00
-- url     : https://prove2.me/submissions/570bc1e3-867a-40c5-8be7-1883aff03a36

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank
open PersistClust.Count

namespace S218PC

/-- `0` is always present, `1` is born at `10`, every `i ≥ 2` is born at `9`. -/
def stg (t : ℝ) : Set ℕ := {i | i = 0 ∨ (i = 1 ∧ t ≤ 10) ∨ (2 ≤ i ∧ t ≤ 9)}

/-- Component label: `1` merges into `0` at levels `≤ 1`. -/
noncomputable def cc (t : ℝ) (x : ℕ) : ℕ := if x = 1 ∧ t ≤ 1 then 0 else x

def JJ (t : ℝ) (x y : ℕ) : Prop := x ∈ stg t ∧ y ∈ stg t ∧ cc t x = cc t y

lemma stg_anti {s t : ℝ} (hst : s ≤ t) : stg t ⊆ stg s := by
  intro i hi
  simp only [stg, Set.mem_setOf_eq] at *
  rcases hi with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, by linarith⟩)
  · exact Or.inr (Or.inr ⟨h1, by linarith⟩)

lemma law : FiltrationLaw stg JJ where
  antitone := fun _ _ h => stg_anti h
  mem := fun _ _ _ h => ⟨h.1, h.2.1⟩
  refl := fun _ _ hx => ⟨hx, hx, rfl⟩
  symm := fun _ _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  trans := fun _ _ _ _ h1 h2 => ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩
  compat := by
    intro s t hst x y h
    refine ⟨stg_anti hst h.1, stg_anti hst h.2.1, ?_⟩
    have h3 := h.2.2
    by_cases ht : t ≤ 1
    · have hs : s ≤ 1 := by linarith
      have e : ∀ z, cc s z = cc t z := by intro z; simp [cc, ht, hs]
      rw [e, e]; exact h3
    · simp only [cc, ht, and_false, if_false] at h3
      rw [h3]

noncomputable def g (s t : ℝ) : ℕ∞ :=
  if s ≤ 9 then ⊤ else if s ≤ 10 then (if 1 < t then 2 else 1) else 1

lemma two_sub_one : (2 : ℕ∞) - 1 = 1 := rfl

lemma r_eq (s t : ℝ) (h : t ≤ s) : rankFn stg JJ s t = g s t := by
  unfold rankFn g
  by_cases h9 : s ≤ 9
  · rw [if_pos h9, Set.encard_eq_top_iff]
    have hinj : Set.InjOn (fun x => {y | JJ t x y}) (Set.Ici 2) := by
      intro x hx y hy hxy
      simp only [Set.mem_Ici] at hx hy
      have hyt : y ∈ stg t := Or.inr (Or.inr ⟨hy, by linarith⟩)
      have hm : y ∈ {z | JJ t y z} := ⟨hyt, hyt, rfl⟩
      have hxy' : {z | JJ t x z} = {z | JJ t y z} := hxy
      rw [← hxy'] at hm
      have := hm.2.2
      simp only [cc] at this
      rw [if_neg (by omega), if_neg (by omega)] at this
      exact this
    refine ((Set.Ici_infinite 2).image hinj).mono (Set.image_mono ?_)
    intro i hi
    exact Or.inr (Or.inr ⟨hi, h9⟩)
  rw [if_neg h9]
  by_cases h10 : s ≤ 10
  · have hS : stg s = {0, 1} := by
      ext i; simp only [stg, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h | ⟨h1, _⟩ | ⟨_, h2⟩)
        · exact Or.inl h
        · exact Or.inr h1
        · exact absurd h2 h9
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h, h10⟩)
    rw [if_pos h10, hS, Set.image_pair]
    have h0t : (0:ℕ) ∈ stg t := Or.inl rfl
    have h1t : (1:ℕ) ∈ stg t := Or.inr (Or.inl ⟨rfl, by linarith⟩)
    by_cases h1 : 1 < t
    · rw [if_pos h1, Set.encard_pair]
      intro he
      have hm : (1:ℕ) ∈ {y | JJ t 1 y} := ⟨h1t, h1t, rfl⟩
      rw [← he] at hm
      have := hm.2.2
      simp [cc, not_le.2 h1] at this
    · rw [if_neg h1]
      have he : {y | JJ t 0 y} = {y | JJ t 1 y} := by
        ext y
        have : t ≤ 1 := not_lt.1 h1
        simp only [JJ, Set.mem_setOf_eq, h0t, h1t, true_and, cc]
        simp [this]
      rw [he, Set.pair_eq_singleton, Set.encard_singleton]
  · have hS : stg s = {0} := by
      ext i; simp only [stg, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro (h | ⟨_, h2⟩ | ⟨_, h2⟩)
        · exact h
        · exact absurd h2 h10
        · exact absurd h2 h9
      · intro h; exact Or.inl h
    rw [if_neg h10, hS, Set.image_singleton, Set.encard_singleton]

lemma mult_cc (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (h : d < b) :
    mult r ((b:EReal), (d:EReal)) = ⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo 0 ((b - d) / 2)),
      ((r (b - ε) (d + ε) - r (b + ε) (d + ε)) - (r (b - ε) (d - ε) - r (b + ε) (d - ε))) := by
  rw [mult, if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_neg (EReal.coe_ne_bot d),
    if_pos (EReal.coe_lt_coe_iff.2 h)]
  simp only [EReal.toReal_coe]

lemma mult_cbot (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r ((b:EReal), ⊥) = ⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ b - ε),
        (r (b - ε) t - r (b + ε) t) := by
  rw [mult, if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_pos rfl]
  simp only [EReal.toReal_coe]

lemma term_eq (b d ε : ℝ) (hε : ε ∈ Set.Ioo 0 ((b - d) / 2)) :
    ((rankFn stg JJ (b - ε) (d + ε) - rankFn stg JJ (b + ε) (d + ε)) -
      (rankFn stg JJ (b - ε) (d - ε) - rankFn stg JJ (b + ε) (d - ε))) =
    ((g (b - ε) (d + ε) - g (b + ε) (d + ε)) - (g (b - ε) (d - ε) - g (b + ε) (d - ε))) := by
  obtain ⟨h1, h2⟩ := hε
  rw [r_eq _ _ (by linarith), r_eq _ _ (by linarith), r_eq _ _ (by linarith),
    r_eq _ _ (by linarith)]

lemma zero_of (b d ε : ℝ) (h : d < b) (hε : ε ∈ Set.Ioo 0 ((b - d) / 2))
    (hz : ((g (b - ε) (d + ε) - g (b + ε) (d + ε)) - (g (b - ε) (d - ε) - g (b + ε) (d - ε))) = 0) :
    mult (rankFn stg JJ) ((b:EReal), (d:EReal)) = 0 := by
  rw [mult_cc _ _ _ h]
  refine le_zero_iff.1 ((iInf₂_le ε hε).trans (le_of_eq ?_))
  rw [term_eq _ _ _ hε, hz]

lemma mult_cc_zero (b d : ℝ) (h : d < b) (hne : ¬ (b = 10 ∧ d = 1)) :
    mult (rankFn stg JJ) ((b:EReal), (d:EReal)) = 0 := by
  have hbd : 0 < b - d := by linarith
  rcases lt_trichotomy b 9 with hb | hb | hb
  · -- b < 9 : B = ⊤
    set ε := min (9 - b) ((b - d) / 4) with hεd
    have e1 : ε ≤ 9 - b := min_le_left _ _
    have e2 : ε ≤ (b - d) / 4 := min_le_right _ _
    have e3 : 0 < ε := lt_min (by linarith) (by linarith)
    refine zero_of b d ε h ⟨e3, by linarith⟩ ?_
    unfold g
    simp only [if_pos (show b + ε ≤ 9 by linarith)]
    simp
  · subst hb
    set ε := (9 - d) / 4 with hεd
    refine zero_of 9 d ε h ⟨by positivity, by linarith⟩ ?_
    unfold g
    simp only [if_pos (show (9:ℝ) - ε ≤ 9 by linarith), if_neg (show ¬ (9:ℝ) + ε ≤ 9 by linarith)]
    split_ifs <;> simp
  · rcases lt_trichotomy b 10 with hb' | hb' | hb'
    · set ε := min (min ((b - 9) / 2) (10 - b)) ((b - d) / 4)
      have e1 : ε ≤ min ((b - 9) / 2) (10 - b) := min_le_left _ _
      have e1a : ε ≤ (b - 9) / 2 := e1.trans (min_le_left _ _)
      have e1b : ε ≤ 10 - b := e1.trans (min_le_right _ _)
      have e2 : ε ≤ (b - d) / 4 := min_le_right _ _
      have e3 : 0 < ε := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      refine zero_of b d ε h ⟨e3, by linarith⟩ ?_
      unfold g
      simp only [if_neg (show ¬ b - ε ≤ 9 by linarith), if_neg (show ¬ b + ε ≤ 9 by linarith),
        if_pos (show b - ε ≤ 10 by linarith), if_pos (show b + ε ≤ 10 by linarith)]
      simp
    · subst hb'
      have hd : d ≠ 1 := fun hd => hne ⟨rfl, hd⟩
      rcases lt_or_gt_of_ne hd with hd | hd
      · set ε := min (min (1/4) ((1 - d) / 2)) ((10 - d) / 4)
        have e1 : ε ≤ min (1/4) ((1 - d) / 2) := min_le_left _ _
        have e1a : ε ≤ 1/4 := e1.trans (min_le_left _ _)
        have e1b : ε ≤ (1 - d) / 2 := e1.trans (min_le_right _ _)
        have e2 : ε ≤ (10 - d) / 4 := min_le_right _ _
        have e3 : 0 < ε := lt_min (lt_min (by norm_num) (by linarith)) (by linarith)
        refine zero_of 10 d ε h ⟨e3, by linarith⟩ ?_
        unfold g
        simp only [if_neg (show ¬ (10:ℝ) - ε ≤ 9 by linarith), if_neg (show ¬ (10:ℝ) + ε ≤ 9 by linarith),
          if_pos (show (10:ℝ) - ε ≤ 10 by linarith), if_neg (show ¬ (10:ℝ) + ε ≤ 10 by linarith),
          if_neg (show ¬ 1 < d + ε by linarith)]
        simp
      · set ε := min (min (1/4) ((d - 1) / 2)) ((10 - d) / 4)
        have e1 : ε ≤ min (1/4) ((d - 1) / 2) := min_le_left _ _
        have e1a : ε ≤ 1/4 := e1.trans (min_le_left _ _)
        have e1b : ε ≤ (d - 1) / 2 := e1.trans (min_le_right _ _)
        have e2 : ε ≤ (10 - d) / 4 := min_le_right _ _
        have e3 : 0 < ε := lt_min (lt_min (by norm_num) (by linarith)) (by linarith)
        refine zero_of 10 d ε h ⟨e3, by linarith⟩ ?_
        unfold g
        simp only [if_neg (show ¬ (10:ℝ) - ε ≤ 9 by linarith), if_neg (show ¬ (10:ℝ) + ε ≤ 9 by linarith),
          if_pos (show (10:ℝ) - ε ≤ 10 by linarith), if_neg (show ¬ (10:ℝ) + ε ≤ 10 by linarith),
          if_pos (show 1 < d + ε by linarith), if_pos (show 1 < d - ε by linarith)]
        simp
    · set ε := min ((b - 10) / 2) ((b - d) / 4)
      have e1 : ε ≤ (b - 10) / 2 := min_le_left _ _
      have e2 : ε ≤ (b - d) / 4 := min_le_right _ _
      have e3 : 0 < ε := lt_min (by linarith) (by linarith)
      refine zero_of b d ε h ⟨e3, by linarith⟩ ?_
      unfold g
      simp only [if_neg (show ¬ b - ε ≤ 9 by linarith), if_neg (show ¬ b + ε ≤ 9 by linarith),
        if_neg (show ¬ b - ε ≤ 10 by linarith), if_neg (show ¬ b + ε ≤ 10 by linarith)]
      simp

lemma mult_cbot_zero (b : ℝ) (hb : b ≠ 9) : mult (rankFn stg JJ) ((b:EReal), ⊥) = 0 := by
  rw [mult_cbot]
  set ε := |b - 9| / 2 with hεd
  have e3 : 0 < ε := by have := abs_pos.2 (sub_ne_zero.2 hb); positivity
  set t := min 1 (b - ε)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ b - ε := min_le_right _ _
  refine le_zero_iff.1 ((iInf₂_le ε e3).trans ((iInf₂_le t ht2).trans (le_of_eq ?_)))
  rw [r_eq _ _ ht2, r_eq _ _ (by linarith)]
  unfold g
  rcases lt_or_gt_of_ne hb with hb | hb
  · have : ε = (9 - b) / 2 := by rw [hεd, abs_of_neg (by linarith)]; ring
    simp only [if_pos (show b - ε ≤ 9 by linarith), if_pos (show b + ε ≤ 9 by linarith)]
    simp
  · have : ε = (b - 9) / 2 := by rw [hεd, abs_of_pos (by linarith)]
    simp only [if_neg (show ¬ b - ε ≤ 9 by linarith), if_neg (show ¬ b + ε ≤ 9 by linarith)]
    simp only [if_neg (show ¬ 1 < t by linarith)]
    split_ifs <;> simp

lemma hFin : {p : EReal × EReal | (mult (rankFn stg JJ)) p ≠ 0}.Finite := by
  refine (Set.toFinite ({(((9:ℝ):EReal), ⊥), (((10:ℝ):EReal), ((1:ℝ):EReal))} :
    Set (EReal × EReal))).subset ?_
  rintro ⟨x, y⟩ hp
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  by_contra hc
  apply hp
  induction x using EReal.rec with
  | bot => simp [mult]
  | top => simp [mult]
  | coe b =>
    induction y using EReal.rec with
    | bot =>
      have : b ≠ 9 := fun h => hc (Or.inl ⟨by rw [h], rfl⟩)
      exact mult_cbot_zero b this
    | top =>
      rw [mult, if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_neg (by simp),
        if_neg (not_lt.2 le_top)]
    | coe d =>
      by_cases hdb : d < b
      · refine mult_cc_zero b d hdb ?_
        rintro ⟨rfl, rfl⟩
        exact hc (Or.inr ⟨rfl, rfl⟩)
      · rw [mult, if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_neg (EReal.coe_ne_bot d),
          if_neg (by rw [EReal.coe_lt_coe_iff]; exact hdb)]

lemma orig_zero : mult (rankFn stg JJ) (((10:ℝ):EReal), ((1:ℝ):EReal)) = 0 := by
  rw [mult_cc _ _ _ (by norm_num)]
  have hε : (2:ℝ) ∈ Set.Ioo 0 ((10 - 1) / 2) := ⟨by norm_num, by norm_num⟩
  refine le_zero_iff.1 ((iInf₂_le 2 hε).trans (le_of_eq ?_))
  rw [term_eq _ _ _ hε]
  unfold g
  norm_num

lemma trunc_ne : mult (truncRank (rankFn stg JJ) (1/2)) (((10:ℝ):EReal), ((1:ℝ):EReal)) ≠ 0 := by
  rw [mult_cc _ _ _ (by norm_num)]
  have key : (1 : ℕ∞) ≤ ⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo 0 (((10:ℝ) - 1) / 2)),
      ((truncRank (rankFn stg JJ) (1/2) (10 - ε) (1 + ε) -
          truncRank (rankFn stg JJ) (1/2) (10 + ε) (1 + ε)) -
        (truncRank (rankFn stg JJ) (1/2) (10 - ε) (1 - ε) -
          truncRank (rankFn stg JJ) (1/2) (10 + ε) (1 - ε))) := by
    refine le_iInf₂ fun ε hε => ?_
    obtain ⟨h1, h2⟩ := hε
    unfold truncRank
    rw [r_eq _ _ (by linarith), r_eq _ _ (by linarith), r_eq _ _ (by linarith),
      r_eq _ _ (by linarith)]
    unfold g
    have hB : ¬ (10:ℝ) + ε ≤ 9 := by linarith
    have hB' : ¬ (10:ℝ) + ε ≤ 10 := by linarith
    have hA2 : (1/2:ℝ) ≤ 10 - ε ∧ 1/2 ≤ 1 + ε := ⟨by linarith, by linarith⟩
    have hB2 : (1/2:ℝ) ≤ 10 + ε ∧ 1/2 ≤ 1 + ε := ⟨by linarith, by linarith⟩
    have hA3 : (10:ℝ) - ε ≤ 10 := by linarith
    have hA4 : (1:ℝ) < 1 + ε := by linarith
    simp only [if_pos hA2, if_pos hB2, if_neg hB, if_neg hB', if_pos hA3, if_pos hA4]
    by_cases hε1 : 10 - ε ≤ 9
    · have hC : ¬ ((1/2:ℝ) ≤ 10 - ε ∧ 1/2 ≤ 1 - ε) := by rintro ⟨_, h⟩; linarith
      have hD : ¬ ((1/2:ℝ) ≤ 10 + ε ∧ 1/2 ≤ 1 - ε) := by rintro ⟨_, h⟩; linarith
      simp only [if_pos hε1, if_neg hC, if_neg hD]
      simp
    · simp only [if_neg hε1]
      by_cases hε2 : ε ≤ 1/2
      · have hC : ((1/2:ℝ) ≤ 10 - ε ∧ 1/2 ≤ 1 - ε) := ⟨by linarith, by linarith⟩
        have hD : ((1/2:ℝ) ≤ 10 + ε ∧ 1/2 ≤ 1 - ε) := ⟨by linarith, by linarith⟩
        have hC2 : ¬ (1:ℝ) < 1 - ε := by linarith
        simp only [if_pos hC, if_pos hD, if_neg hC2]
        simp [two_sub_one]
      · have hC : ¬ ((1/2:ℝ) ≤ 10 - ε ∧ 1/2 ≤ 1 - ε) := by rintro ⟨_, h⟩; linarith
        have hD : ¬ ((1/2:ℝ) ≤ 10 + ε ∧ 1/2 ≤ 1 - ε) := by rintro ⟨_, h⟩; linarith
        simp only [if_neg hC, if_neg hD]
        simp [two_sub_one]
  intro h
  rw [h] at key
  exact absurd key (by simp)

end S218PC

open S218PC in
theorem solution : ¬ (∀ {ι : Type} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) (α : ℝ)
    (hFin : {p : EReal × EReal | (mult (rankFn stage J)) p ≠ 0}.Finite),
    ∀ p ∈ QNE α, mult (rankFn stage J) p = mult (truncRank (rankFn stage J) α) p) := by
  intro H
  have hQ : (((10:ℝ):EReal), ((1:ℝ):EReal)) ∈ QNE (1/2) :=
    ⟨EReal.coe_lt_coe_iff.2 (by norm_num), EReal.coe_lt_coe_iff.2 (by norm_num)⟩
  have := H stg JJ law (1/2) hFin _ hQ
  rw [orig_zero] at this
  exact trunc_ne this.symm
