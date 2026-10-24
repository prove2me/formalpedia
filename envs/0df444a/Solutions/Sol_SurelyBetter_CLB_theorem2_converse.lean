-- Prove2me | solution 1 for SurelyBetter.CLB.theorem2_converse
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:15:29.282967+00:00
-- url     : https://prove2.me/submissions/9d4088f8-e8de-4349-9d37-d40bf391f68b

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Theorems.Thm_SurelyBetter_CLB_theorem2_max_rep

open SurelyBetter.CLB Supermodularity.Lattices

namespace SurelyBetter.CLB.ConverseProof

def argmax (F : ℝ → ℝ) : Set ℝ :=
  {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ b ∈ Set.Icc (0 : ℝ) 1, F b ≤ F a}

lemma argmax_order (F G : ℝ → ℝ)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≤ t * F 1 + (1 - t) * F 0)
    (hG : ∀ t ∈ Set.Icc (0 : ℝ) 1, G t ≤ t * G 1 + (1 - t) * G 0)
    (h0 : F 0 = G 0) (h1 : F 1 < G 1 ∨ F = G) :
    InducedSetOrder (argmax F) (argmax G) := by
  intro a ha b hb
  by_cases hab : a ≤ b
  · simpa only [inf_eq_left.mpr hab, sup_eq_right.mpr hab] using And.intro ha hb
  have hba : b < a := lt_of_not_ge hab
  rcases h1 with hstrict | rfl
  · have ha0 : 0 < a := lt_of_le_of_lt hb.1.1 hba
    have hb1 : b < 1 := lt_of_lt_of_le hba ha.1.2
    have hF0 := ha.2 0 (by constructor <;> norm_num)
    have hG1 := hb.2 1 (by constructor <;> norm_num)
    have hFc := hF a ha.1
    have hGc := hG b hb.1
    have hF01 : F 0 ≤ F 1 := by nlinarith
    have hG10 : G 1 ≤ G 0 := by nlinarith
    linarith
  · simpa only [inf_eq_right.mpr (le_of_lt hba), sup_eq_left.mpr (le_of_lt hba)]
      using And.intro hb ha

def score (r s a b : ℝ) : ℝ :=
  max (r * a + (1 - r) * b) ((1 - s) * a + s * b)

def along (r s a b c d t : ℝ) : ℝ :=
  score r s (t * a + (1 - t) * c) (t * b + (1 - t) * d)

lemma along_zero (r s a b c d : ℝ) : along r s a b c d 0 = score r s c d := by
  simp [along]

lemma along_one (r s a b c d : ℝ) : along r s a b c d 1 = score r s a b := by
  simp [along]

lemma along_chord (r s a b c d t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    along r s a b c d t ≤ t * along r s a b c d 1 +
      (1 - t) * along r s a b c d 0 := by
  rw [along_one, along_zero]
  unfold along score
  apply max_le
  · have h1 := mul_le_mul_of_nonneg_left
      (le_max_left (r * a + (1 - r) * b) ((1 - s) * a + s * b)) ht.1
    have h0 := mul_le_mul_of_nonneg_left
      (le_max_left (r * c + (1 - r) * d) ((1 - s) * c + s * d))
      (sub_nonneg.mpr ht.2)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left
      (le_max_right (r * a + (1 - r) * b) ((1 - s) * a + s * b)) ht.1
    have h0 := mul_le_mul_of_nonneg_left
      (le_max_right (r * c + (1 - r) * d) ((1 - s) * c + s * d))
      (sub_nonneg.mpr ht.2)
    nlinarith

lemma score_strict (r s a b a' b' : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (ha : a ≤ a') (hb : b ≤ b') (hstrict : a < a' ∨ b < b') :
    score r s a b < score r s a' b' := by
  have hfirst : r * a + (1 - r) * b < r * a' + (1 - r) * b' := by
    rcases hstrict with h | h
    · nlinarith [mul_pos hr0 (sub_pos.mpr h),
        mul_nonneg (le_of_lt (sub_pos.mpr hr1)) (sub_nonneg.mpr hb)]
    · nlinarith [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr h),
        mul_nonneg (le_of_lt hr0) (sub_nonneg.mpr ha)]
  have hsecond : (1 - s) * a + s * b < (1 - s) * a' + s * b' := by
    rcases hstrict with h | h
    · nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr h),
        mul_nonneg (le_of_lt hs0) (sub_nonneg.mpr hb)]
    · nlinarith [mul_pos hs0 (sub_pos.mpr h),
        mul_nonneg (le_of_lt (sub_pos.mpr hs1)) (sub_nonneg.mpr ha)]
  exact max_lt (lt_of_lt_of_le hfirst (le_max_left _ _))
    (lt_of_lt_of_le hsecond (le_max_right _ _))

lemma mix_binary {S : Type*} (E : Set S) (a b c d t : ℝ) :
    mix t (binProf E a b) (binProf E c d) =
      binProf E (t * a + (1 - t) * c) (t * b + (1 - t) * d) := by
  ext x
  by_cases hx : x ∈ E <;> simp [mix, binProf, hx]

lemma binary_profile {S : Type*} (U : Set ℝ) (E : Set S)
    {a b : ℝ} (ha : a ∈ U) (hb : b ∈ U) : binProf E a b ∈ Profiles U := by
  intro x
  by_cases hx : x ∈ E <;> simp [binProf, hx, ha, hb]

lemma opt_binary {S : Type*} (U : Set ℝ) (hU : Convex ℝ U)
    (V : (S → ℝ) → ℝ) (E : Set S) (r s : ℝ)
    (hrep : ∀ a ∈ U, ∀ b ∈ U, ∀ a' ∈ U, ∀ b' ∈ U,
      (V (binProf E a b) ≤ V (binProf E a' b') ↔ score r s a b ≤ score r s a' b'))
    {a b c d : ℝ} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U) :
    optMix V (binProf E a b) (binProf E c d) = argmax (along r s a b c d) := by
  ext t
  simp only [optMix, argmax, Set.mem_ofPred_eq]
  apply and_congr_right
  intro ht
  apply forall₂_congr
  intro z hz
  rw [mix_binary, mix_binary]
  apply hrep
  · exact hU ha hc hz.1 (sub_nonneg.mpr hz.2) (by ring)
  · exact hU hb hd hz.1 (sub_nonneg.mpr hz.2) (by ring)
  · exact hU ha hc ht.1 (sub_nonneg.mpr ht.2) (by ring)
  · exact hU hb hd ht.1 (sub_nonneg.mpr ht.2) (by ring)

lemma converse_of_rep {S : Type*} (U : Set ℝ) (hU : Convex ℝ U)
    (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ) (hV : IsCLinBisep U V ρ) (E : Set S)
    (hrep : ∀ a ∈ U, ∀ b ∈ U, ∀ a' ∈ U, ∀ b' ∈ U,
      (V (binProf E a b) ≤ V (binProf E a' b') ↔
        score (ρ E) (ρ Eᶜ) a b ≤ score (ρ E) (ρ Eᶜ) a' b'))
    (hcond : max (ρ E) (ρ Eᶜ) < 1 ∨ min (ρ E) (ρ Eᶜ) = 0)
    (hsum : 1 ≤ ρ E + ρ Eᶜ) : MOMOn V (measE U E) := by
  have hcap1 (F : Set S) : ρ F ≤ 1 := by
    rw [← hV.capacity.2.1]
    exact hV.capacity.2.2 F Set.univ (Set.subset_univ F)
  rintro f ⟨a, ha, b, hb, rfl⟩ f' ⟨a', ha', b', hb', rfl⟩
    g ⟨c, hc, d, hd, rfl⟩ hff'
  rw [opt_binary U hU V E (ρ E) (ρ Eᶜ) hrep ha hb hc hd,
    opt_binary U hU V E (ρ E) (ρ Eᶜ) hrep ha' hb' hc hd]
  apply argmax_order
      (along (ρ E) (ρ Eᶜ) a b c d) (along (ρ E) (ρ Eᶜ) a' b' c d)
  · exact fun t ht => along_chord _ _ _ _ _ _ t ht
  · exact fun t ht => along_chord _ _ _ _ _ _ t ht
  · simp only [along_zero]
  rcases hcond with hcond | hcond
  · have hr1 : ρ E < 1 := lt_of_le_of_lt (le_max_left _ _) hcond
    have hs1 : ρ Eᶜ < 1 := lt_of_le_of_lt (le_max_right _ _) hcond
    have hr0 : 0 < ρ E := by linarith
    have hs0 : 0 < ρ Eᶜ := by linarith
    obtain ⟨x, hx⟩ : E.Nonempty := Set.nonempty_iff_ne_empty.mpr (by
      intro h
      rw [h, hV.capacity.1] at hr0
      exact lt_irrefl _ hr0)
    obtain ⟨y, hy⟩ : Eᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr (by
      intro h
      rw [h, hV.capacity.1] at hs0
      exact lt_irrefl _ hs0)
    have haa' : a ≤ a' := by simpa [binProf, hx] using hff' x
    have hbb' : b ≤ b' := by simpa [binProf, show y ∉ E from hy] using hff' y
    rcases lt_or_eq_of_le haa' with hlt | rfl
    · left
      simpa only [along_one] using
        score_strict _ _ _ _ _ _ hr0 hr1 hs0 hs1 haa' hbb' (Or.inl hlt)
    rcases lt_or_eq_of_le hbb' with hlt | rfl
    · left
      simpa only [along_one] using
        score_strict _ _ _ _ _ _ hr0 hr1 hs0 hs1 le_rfl hbb' (Or.inr hlt)
    · exact Or.inr rfl
  · have hlin (a b c d t : ℝ) : along (ρ E) (ρ Eᶜ) a b c d t =
        t * score (ρ E) (ρ Eᶜ) a b + (1 - t) * score (ρ E) (ρ Eᶜ) c d := by
      rcases le_total (ρ E) (ρ Eᶜ) with hle | hle
      · have hr : ρ E = 0 := by simpa only [min_eq_left hle] using hcond
        have hs : ρ Eᶜ = 1 := by have := hcap1 Eᶜ; linarith
        simp [along, score, hr, hs]
      · have hs : ρ Eᶜ = 0 := by simpa only [min_eq_right hle] using hcond
        have hr : ρ E = 1 := by have := hcap1 E; linarith
        simp [along, score, hr, hs]
    have hmono : score (ρ E) (ρ Eᶜ) a b ≤ score (ρ E) (ρ Eᶜ) a' b' :=
      (hrep a ha b hb a' ha' b' hb').mp
        (hV.monotone _ (binary_profile U E ha hb) _ (binary_profile U E ha' hb') hff')
    rcases lt_or_eq_of_le hmono with hlt | heq
    · left
      simpa only [along_one] using hlt
    · right
      funext t
      rw [hlin, hlin, heq]

end SurelyBetter.CLB.ConverseProof

theorem solution {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) :
    (max (ρ E) (ρ Eᶜ) < 1 ∨ min (ρ E) (ρ Eᶜ) = 0) → 1 ≤ ρ E + ρ Eᶜ →
      MOMOn V (measE U E) := by
  intro hcond hsum
  apply ConverseProof.converse_of_rep U hU V ρ hV E ?_ hcond hsum
  simpa only [ConverseProof.score] using theorem2_max_rep U hU hU2 V ρ hV E hsum
