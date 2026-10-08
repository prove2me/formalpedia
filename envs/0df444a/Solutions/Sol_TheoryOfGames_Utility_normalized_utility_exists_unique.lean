-- Prove2me | solution 1 for TheoryOfGames.Utility.normalized_utility_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:17:34.778923+00:00
-- url     : https://prove2.me/submissions/18b01294-2da8-4e89-82f4-ae96fe81f63e

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem
import Definitions.Def_TheoryOfGames_Utility_IsNumericalUtility



namespace TheoryOfGames.Utility

open Classical

set_option linter.unusedSectionVars false

namespace VNMAux

variable {U : Type*} (S : UtilitySystem U)

lemma gt_irrefl (u : U) : ¬ S.gt u u := by
  rcases S.complete u u with h | h | h
  · exact h.2.1
  · exact absurd rfl h.2.1
  · exact absurd rfl h.2.1

lemma gt_asymm {u v : U} (h : S.gt u v) : ¬ S.gt v u := by
  rcases S.complete u v with h' | h' | h'
  · exact absurd h h'.2.1
  · exact h'.2.2
  · exact absurd h h'.2.2

lemma gt_tri (u v : U) : u = v ∨ S.gt u v ∨ S.gt v u := by
  rcases S.complete u v with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

noncomputable def toLO : LinearOrder U where
  le u v := u = v ∨ S.gt v u
  lt u v := S.gt v u
  le_refl u := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    exact Or.inr (S.trans _ _ _ hbc hab)
  le_antisymm a b hab hba := by
    rcases hab with rfl | hab
    · rfl
    rcases hba with rfl | hba
    · rfl
    exact absurd hab (gt_asymm S hba)
  le_total a b := by
    rcases gt_tri S a b with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inr h)
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (h' | h')
      · subst h'; exact gt_irrefl S _ h
      · exact gt_asymm S h h'
    · rintro ⟨h1 | h1, h2⟩
      · subst h1; exact absurd (Or.inl rfl) h2
      · exact h1
  toDecidableLE := Classical.decRel _

end VNMAux

namespace VNMCore

variable {U : Type*} [LinearOrder U] (S : UtilitySystem U) (hS : ∀ u v : U, S.gt u v ↔ v < u)

noncomputable def P (u v : U) (t : ℝ) : U :=
  if h : 0 < t ∧ t < 1 then S.mix ⟨t, h⟩ u v else if t ≤ 0 then v else u

lemma P_of {u v : U} {t : ℝ} (h : 0 < t ∧ t < 1) : P S u v t = S.mix ⟨t, h⟩ u v := dif_pos h

lemma mix_eq_P (α : OpenUnit) (u v : U) : S.mix α u v = P S u v α := by
  rw [P_of S α.2]

lemma P_le0 {u v : U} {t : ℝ} (h : t ≤ 0) : P S u v t = v := by
  unfold P; rw [dif_neg (by intro h'; linarith [h'.1]), if_pos h]

lemma P_ge1 {u v : U} {t : ℝ} (h : 1 ≤ t) : P S u v t = u := by
  unfold P; rw [dif_neg (by intro h'; linarith [h'.2]), if_neg (by linarith)]

lemma P_zero (u v : U) : P S u v 0 = v := P_le0 S le_rfl
lemma P_one (u v : U) : P S u v 1 = u := P_ge1 S le_rfl

lemma Pcomm (u v : U) (t : ℝ) : P S u v t = P S v u (1 - t) := by
  by_cases h : 0 < t ∧ t < 1
  · have h' : 0 < 1 - t ∧ 1 - t < 1 := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [P_of S h, P_of S h', S.mix_comm]
    rfl
  · rcases le_or_gt t 0 with h0 | h0
    · rw [P_le0 S h0, P_ge1 S (by linarith)]
    · have : 1 ≤ t := by by_contra hc; exact h ⟨h0, by linarith⟩
      rw [P_ge1 S this, P_le0 S (by linarith)]

lemma PMM_open {u v : U} {α β : ℝ} (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1) :
    P S (P S u v β) v α = P S u v (α * β) := by
  have hab : 0 < α * β ∧ α * β < 1 := ⟨mul_pos hα.1 hβ.1, by nlinarith⟩
  rw [P_of S hβ, P_of S hα, S.mix_mix, P_of S hab]
  rfl

include hS in
lemma P_between {a b : U} (hab : a < b) {t : ℝ} (ht : 0 < t ∧ t < 1) :
    a < P S a b t ∧ P S a b t < b := by
  rw [P_of S ht]
  constructor
  · exact (hS _ _).1 (S.lt_mix_of_lt _ a b ((hS _ _).2 hab))
  · rw [S.mix_comm]
    exact (hS _ _).1 (S.mix_lt_of_gt _ b a ((hS _ _).2 hab))

include hS in
lemma PI (u : U) (t : ℝ) : P S u u t = u := by
  have key : ∀ β, 0 < β ∧ β < 1 → P S u u β ≠ u → ∀ α, 0 < α ∧ α < 1 →
      P S u u (α * β) ≠ u ∧ P S u u (α * β) ≠ P S u u β := by
    intro β hβ hne α hα
    rw [← PMM_open S hα hβ]
    rcases lt_or_gt_of_ne hne with h | h
    · have := P_between S hS h hα
      exact ⟨this.2.ne, this.1.ne'⟩
    · rw [Pcomm S (P S u u β) u α]
      have := P_between S hS h (t := 1 - α) ⟨by linarith [hα.2], by linarith [hα.1]⟩
      exact ⟨this.1.ne', this.2.ne⟩
  have sym : ∀ β, P S u u β = P S u u (1 - β) := fun β => Pcomm S u u β
  have half : ∀ β, 1 / 2 < β → β < 1 → P S u u β = u := by
    intro β h1 h2
    by_contra hne
    have hα : 0 < (1 - β) / β ∧ (1 - β) / β < 1 := by
      constructor
      · apply div_pos <;> linarith
      · rw [div_lt_one (by linarith)]; linarith
    have := (key β ⟨by linarith, h2⟩ hne _ hα).2
    rw [div_mul_cancel₀ _ (by linarith), ← sym] at this
    exact this rfl
  by_cases h : 0 < t ∧ t < 1
  · rcases lt_or_ge (1 / 2) t with h1 | h1
    · exact half t h1 h.2
    · by_contra hne
      have := (key t h hne (1 / 2) ⟨by norm_num, by norm_num⟩).1
      rw [sym] at this
      exact this (half _ (by linarith) (by linarith [h.1]))
  · unfold P; rw [dif_neg h]; split_ifs <;> rfl

include hS in
lemma PMM {u v : U} {α β : ℝ} (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) :
    P S (P S u v β) v α = P S u v (α * β) := by
  rcases eq_or_lt_of_le hα.1 with h0 | h0
  · subst h0; simp [P_zero]
  rcases eq_or_lt_of_le hα.2 with h1 | h1
  · subst h1; simp [P_one]
  rcases eq_or_lt_of_le hβ.1 with h2 | h2
  · subst h2; simp [P_zero, PI S hS]
  rcases eq_or_lt_of_le hβ.2 with h3 | h3
  · subst h3; simp [P_one]
  exact PMM_open S ⟨h0, h1⟩ ⟨h2, h3⟩

include hS in
lemma PL {a v : U} {α δ : ℝ} (hα : 0 ≤ α ∧ α ≤ 1) (hδ : 0 ≤ δ ∧ δ ≤ 1) :
    P S a (P S a v δ) α = P S a v (α + (1 - α) * δ) := by
  rw [Pcomm S a (P S a v δ) α, Pcomm S a v δ,
    PMM S hS ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩, Pcomm S v a]
  congr 1; ring

include hS in
lemma PG_aux {a b : U} {α β γ : ℝ} (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1)
    (hγ : 0 ≤ γ ∧ γ ≤ 1) (hγβ : γ ≤ β) :
    P S (P S a b β) (P S a b γ) α = P S a b (α * β + (1 - α) * γ) := by
  rcases eq_or_lt_of_le hβ.1 with h0 | h0
  · subst h0
    have : γ = 0 := le_antisymm hγβ hγ.1
    subst this
    simp [P_zero, PI S hS]
  have hq : 0 ≤ γ / β ∧ γ / β ≤ 1 :=
    ⟨div_nonneg hγ.1 h0.le, by rw [div_le_one h0]; exact hγβ⟩
  have hγ' : P S a b γ = P S (P S a b β) b (γ / β) := by
    rw [PMM S hS hq hβ, div_mul_cancel₀ _ h0.ne']
  rw [hγ', PL S hS hα hq, PMM S hS ⟨by nlinarith, by nlinarith⟩ hβ]
  congr 1
  field_simp

include hS in
lemma PG {a b : U} {α β γ : ℝ} (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1)
    (hγ : 0 ≤ γ ∧ γ ≤ 1) :
    P S (P S a b β) (P S a b γ) α = P S a b (α * β + (1 - α) * γ) := by
  rcases le_or_gt γ β with h | h
  · exact PG_aux S hS hα hβ hγ h
  · rw [Pcomm S, PG_aux S hS ⟨by linarith, by linarith⟩ hγ hβ h.le]
    congr 1; ring


noncomputable def M (a b : U) (t : ℝ) : U := P S a b (1 - t)

lemma M_zero (a b : U) : M S a b 0 = a := by simp [M, P_one]
lemma M_one (a b : U) : M S a b 1 = b := by simp [M, P_zero]

include hS in
lemma M_mix {a b : U} {p q s : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) :
    P S (M S a b p) (M S a b q) s = M S a b (s * p + (1 - s) * q) := by
  unfold M
  rw [PG S hS ⟨hs.1, hs.2⟩ ⟨by linarith [hp.2], by linarith [hp.1]⟩
    ⟨by linarith [hq.2], by linarith [hq.1]⟩]
  congr 1; ring

include hS in
lemma M_strict {a b : U} (hab : a < b) : StrictMonoOn (M S a b) (Set.Icc 0 1) := by
  intro s hs t ht hst
  unfold M
  have h1s : 0 < 1 - s := by linarith [ht.2]
  have hq : 0 ≤ (1 - t) / (1 - s) ∧ (1 - t) / (1 - s) ≤ 1 :=
    ⟨div_nonneg (by linarith [ht.2]) h1s.le, by rw [div_le_one h1s]; linarith⟩
  have heq : P S a b (1 - t) = P S (P S a b (1 - s)) b ((1 - t) / (1 - s)) := by
    rw [PMM S hS hq ⟨h1s.le, by linarith [hs.1]⟩, div_mul_cancel₀ _ h1s.ne']
  rw [heq]
  have hc : P S a b (1 - s) < b := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; simp [P_one]; exact hab
    · exact (P_between S hS hab ⟨h1s, by linarith⟩).2
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h; simp [P_zero]; exact hc
  · exact (P_between S hS hc ⟨div_pos (by linarith) h1s, by
      rw [div_lt_one h1s]; linarith⟩).1

include hS in
lemma M_surj {a b w : U} (hab : a < b) (haw : a ≤ w) (hwb : w ≤ b) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, M S a b t = w := by
  rcases eq_or_lt_of_le haw with h | haw
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [M_zero, h]⟩
  rcases eq_or_lt_of_le hwb with h | hwb
  · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [M_one, h]⟩
  have hmono := M_strict S hS hab
  set A : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ M S a b t < w} with hA
  have h0A : (0:ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, by rw [M_zero]; exact haw⟩
  have hbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  have hne : A.Nonempty := ⟨0, h0A⟩
  set τ := sSup A with hτ
  have hτ0 : 0 ≤ τ := le_csSup hbdd h0A
  have hτ1 : τ ≤ 1 := csSup_le hne (fun t ht => ht.1.2)
  refine ⟨τ, ⟨hτ0, hτ1⟩, ?_⟩
  rcases lt_trichotomy (M S a b τ) w with hlt | heq | hgt
  · exfalso
    have hτ1' : τ < 1 := by
      rcases eq_or_lt_of_le hτ1 with h | h
      · rw [h, M_one] at hlt; exact absurd hlt (not_lt.2 hwb.le)
      · exact h
    obtain ⟨α, hα⟩ := S.exists_mix_lt (M S a b τ) b w ((hS _ _).2 hlt) ((hS _ _).2 hwb)
    have hα' := (hS _ _).1 hα
    rw [mix_eq_P] at hα'
    have hαI := α.2
    have : P S (M S a b τ) b α = M S a b (1 - α * (1 - τ)) := by
      unfold M
      rw [PMM S hS ⟨hαI.1.le, hαI.2.le⟩ ⟨by linarith, by linarith⟩]
      congr 1; ring
    rw [this] at hα'
    have hmem : 1 - (α:ℝ) * (1 - τ) ∈ A :=
      ⟨⟨by nlinarith [hαI.2], by nlinarith [hαI.1]⟩, hα'⟩
    have := le_csSup hbdd hmem
    nlinarith [hαI.2]
  · exact heq
  · exfalso
    have hτ0' : 0 < τ := by
      rcases eq_or_lt_of_le hτ0 with h | h
      · rw [← h, M_zero] at hgt; exact absurd hgt (not_lt.2 haw.le)
      · exact h
    obtain ⟨α, hα⟩ := S.exists_mix_gt (M S a b τ) a w ((hS _ _).2 hgt) ((hS _ _).2 haw)
    have hα' := (hS _ _).1 hα
    rw [mix_eq_P] at hα'
    have hαI := α.2
    have : P S (M S a b τ) a α = M S a b (α * τ) := by
      unfold M
      rw [Pcomm S a b (1 - τ), sub_sub_cancel, PMM S hS ⟨hαI.1.le, hαI.2.le⟩ ⟨hτ0, hτ1⟩,
        Pcomm S b a]
    rw [this] at hα'
    have hmemI : (α:ℝ) * τ ∈ Set.Icc (0:ℝ) 1 := ⟨by nlinarith [hαI.1], by nlinarith [hαI.2]⟩
    have : τ ≤ α * τ := by
      apply csSup_le hne
      intro t ht
      exact ((hmono.lt_iff_lt ht.1 hmemI).1 (lt_trans ht.2 hα')).le
    nlinarith [hαI.2]

noncomputable def coord (a b w : U) : ℝ :=
  if h : ∃ t ∈ Set.Icc (0:ℝ) 1, M S a b t = w then h.choose else 0

include hS in
lemma coord_spec {a b w : U} (hab : a < b) (haw : a ≤ w) (hwb : w ≤ b) :
    coord S a b w ∈ Set.Icc (0:ℝ) 1 ∧ M S a b (coord S a b w) = w := by
  have h := M_surj S hS hab haw hwb
  unfold coord
  rw [dif_pos h]
  exact h.choose_spec

include hS in
lemma M_mem {a b : U} (hab : a < b) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    a ≤ M S a b t ∧ M S a b t ≤ b := by
  have hm := (M_strict S hS hab).monotoneOn
  constructor
  · have := hm ⟨le_rfl, zero_le_one⟩ ht ht.1
    rwa [M_zero] at this
  · have := hm ht ⟨zero_le_one, le_rfl⟩ ht.2
    rwa [M_one] at this

include hS in
lemma coord_M {a b : U} (hab : a < b) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    coord S a b (M S a b t) = t := by
  have hm := M_mem S hS hab ht
  have h := coord_spec S hS hab hm.1 hm.2
  exact (M_strict S hS hab).injOn h.1 ht h.2

include hS in
lemma coord_lt {a b x y : U} (hab : a < b) (hax : a ≤ x) (hyb : y ≤ b) (hxy : x < y) :
    coord S a b x < coord S a b y := by
  have hx := coord_spec S hS hab hax (hxy.le.trans hyb)
  have hy := coord_spec S hS hab (hax.trans hxy.le) hyb
  rw [← (M_strict S hS hab).lt_iff_lt hx.1 hy.1, hx.2, hy.2]
  exact hxy

include hS in
lemma coordK {a b c d w : U} (hab : a < b) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hcw : c ≤ w) (hwd : w ≤ d) :
    coord S a b w = coord S a b c + coord S c d w * (coord S a b d - coord S a b c) := by
  have hc := coord_spec S hS hab hac (hcd.le.trans hdb)
  have hd := coord_spec S hS hab (hac.trans hcd.le) hdb
  have hw := coord_spec S hS hcd hcw hwd
  have : w = M S a b ((1 - coord S c d w) * coord S a b c +
      (1 - (1 - coord S c d w)) * coord S a b d) := by
    rw [← M_mix S hS hc.1 hd.1 ⟨by linarith [hw.1.2], by linarith [hw.1.1]⟩, hc.2, hd.2]
    exact hw.2.symm
  have hmem : (1 - coord S c d w) * coord S a b c +
      (1 - (1 - coord S c d w)) * coord S a b d ∈ Set.Icc (0:ℝ) 1 := by
    obtain ⟨⟨h1, h2⟩, _⟩ := hc; obtain ⟨⟨h3, h4⟩, _⟩ := hd; obtain ⟨⟨h5, h6⟩, _⟩ := hw
    constructor <;> nlinarith
  conv_lhs => rw [this]
  rw [coord_M S hS hab hmem]
  ring

noncomputable def rr (u0 u1 a b w : U) : ℝ :=
  (coord S a b w - coord S a b u0) / (coord S a b u1 - coord S a b u0)

include hS in
lemma rr_indep {u0 u1 a b a' b' w : U} (h01 : u0 < u1) (ha : a' ≤ a) (hb : b ≤ b')
    (ha0 : a ≤ u0) (hb1 : u1 ≤ b) (haw : a ≤ w) (hwb : w ≤ b) :
    rr S u0 u1 a' b' w = rr S u0 u1 a b w := by
  have hab : a < b := lt_of_le_of_lt ha0 (lt_of_lt_of_le h01 hb1)
  have hab' : a' < b' := lt_of_le_of_lt ha (lt_of_lt_of_le hab hb)
  have k := fun x (h1 : a ≤ x) (h2 : x ≤ b) => coordK S hS hab' ha hab hb h1 h2
  have hD : 0 < coord S a' b' b - coord S a' b' a := by
    have := coord_lt S hS hab' ha hb hab; linarith
  have hD2 : 0 < coord S a b u1 - coord S a b u0 := sub_pos.2 (coord_lt S hS hab ha0 hb1 h01)
  unfold rr
  rw [k w haw hwb, k u0 ha0 (h01.le.trans hb1), k u1 (ha0.trans h01.le) hb1]
  rw [div_eq_div_iff (by nlinarith) hD2.ne']
  ring

noncomputable def hf (u0 u1 w : U) : ℝ := rr S u0 u1 (min w u0) (max w u1) w

include hS in
lemma hf_eq {u0 u1 a b w : U} (h01 : u0 < u1) (ha0 : a ≤ u0) (hb1 : u1 ≤ b) (haw : a ≤ w)
    (hwb : w ≤ b) : hf S u0 u1 w = rr S u0 u1 a b w := by
  unfold hf
  rw [← rr_indep S hS h01 (le_min haw ha0) (max_le hwb hb1) (min_le_right _ _)
    (le_max_right _ _) (min_le_left _ _) (le_max_left _ _)]

lemma cmb_eq (γ : OpenUnit) (u v : U) : S.cmb γ u v = M S u v γ := by
  unfold UtilitySystem.cmb M
  rw [mix_eq_P]
  rfl

include hS in
theorem norm_core (u0 u1 : U) (h01 : u0 < u1) :
    ∃ h : U → ℝ, (h u0 = 0 ∧ h u1 = 1 ∧ (∀ u v : U, u < v → h u < h v) ∧
      ∀ (γ : OpenUnit) (u v : U), h (S.cmb γ u v) = (1 - (γ:ℝ)) * h u + (γ:ℝ) * h v) ∧
      ∀ h₁ : U → ℝ, h₁ u0 = 0 → h₁ u1 = 1 →
        (∀ (γ : OpenUnit) (u v : U), u < v →
          h₁ (S.cmb γ u v) = (1 - (γ : ℝ)) * h₁ u + (γ : ℝ) * h₁ v) → h₁ = h := by
  refine ⟨hf S u0 u1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hf_eq S hS h01 le_rfl le_rfl le_rfl h01.le]; unfold rr; simp
  · rw [hf_eq S hS h01 le_rfl le_rfl h01.le le_rfl]; unfold rr
    have := coord_lt S hS h01 le_rfl le_rfl h01
    rw [div_self (by linarith)]
  · intro u v huv
    have hab : min u u0 < max v u1 := lt_of_le_of_lt (min_le_right _ _)
      (lt_of_lt_of_le h01 (le_max_right _ _))
    rw [hf_eq S hS h01 (min_le_right u u0) (le_max_right v u1) (min_le_left _ _)
      (huv.le.trans (le_max_left _ _)),
      hf_eq S hS h01 (min_le_right u u0) (le_max_right v u1)
      ((min_le_left _ _).trans huv.le) (le_max_left _ _)]
    unfold rr
    apply div_lt_div_of_pos_right _ (by
      have := coord_lt S hS hab (min_le_right u u0) (le_max_right v u1) h01; linarith)
    have := coord_lt S hS hab (min_le_left u u0) (le_max_left v u1) huv
    linarith
  · intro γ u v
    set a := min (min u v) u0
    set b := max (max u v) u1
    have ha0 : a ≤ u0 := min_le_right _ _
    have hb1 : u1 ≤ b := le_max_right _ _
    have hab : a < b := lt_of_le_of_lt ha0 (lt_of_lt_of_le h01 hb1)
    have hau : a ≤ u := (min_le_left _ _).trans (min_le_left _ _)
    have hav : a ≤ v := (min_le_left _ _).trans (min_le_right _ _)
    have hub : u ≤ b := (le_max_left u v).trans (le_max_left _ _)
    have hvb : v ≤ b := (le_max_right u v).trans (le_max_left _ _)
    have hu := coord_spec S hS hab hau hub
    have hv := coord_spec S hS hab hav hvb
    have hγ := γ.2
    have hγ' : (1 - (γ:ℝ)) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hγ.2], by linarith [hγ.1]⟩
    have hx : S.cmb γ u v = M S a b ((1 - γ) * coord S a b u + (1 - (1 - γ)) * coord S a b v) := by
      rw [cmb_eq, ← M_mix S hS hu.1 hv.1 hγ', hu.2, hv.2]
      rfl
    have hmem : (1 - (γ:ℝ)) * coord S a b u + (1 - (1 - γ)) * coord S a b v ∈
        Set.Icc (0:ℝ) 1 := by
      obtain ⟨⟨h1, h2⟩, _⟩ := hu; obtain ⟨⟨h3, h4⟩, _⟩ := hv
      constructor <;> nlinarith [hγ.1, hγ.2]
    have hm := M_mem S hS hab hmem
    rw [hx, hf_eq S hS h01 ha0 hb1 hm.1 hm.2, hf_eq S hS h01 ha0 hb1 hau hub,
      hf_eq S hS h01 ha0 hb1 hav hvb]
    unfold rr
    rw [coord_M S hS hab hmem]
    ring
  · intro h₁ e0 e1 hlin
    funext w
    set a := min w u0
    set b := max w u1
    have ha0 : a ≤ u0 := min_le_right _ _
    have hb1 : u1 ≤ b := le_max_right _ _
    have hab : a < b := lt_of_le_of_lt ha0 (lt_of_lt_of_le h01 hb1)
    have aff : ∀ t ∈ Set.Icc (0:ℝ) 1, h₁ (M S a b t) = (1 - t) * h₁ a + t * h₁ b := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simp [M_zero]
      rcases eq_or_lt_of_le ht.2 with h' | h'
      · subst h'; simp [M_one]
      have := hlin ⟨t, h, h'⟩ a b hab
      rw [cmb_eq] at this
      exact this
    have c0 := coord_spec S hS hab ha0 (h01.le.trans hb1)
    have c1 := coord_spec S hS hab (ha0.trans h01.le) hb1
    have cw := coord_spec S hS hab (min_le_left _ _) (le_max_left _ _)
    have E0 := aff _ c0.1
    have E1 := aff _ c1.1
    have EW := aff _ cw.1
    rw [c0.2, e0] at E0
    rw [c1.2, e1] at E1
    rw [cw.2] at EW
    show h₁ w = rr S u0 u1 a b w
    have hD := coord_lt S hS hab ha0 hb1 h01
    unfold rr
    rw [eq_div_iff (by linarith), EW]
    linear_combination -(coord S a b u1 - coord S a b u0) * E0 -
      (coord S a b w - coord S a b u0) * (E1 - E0)

include hS in
theorem goal_core :
    (∃ v : U → ℝ, IsNumericalUtility S v) ∧
      ∀ v v' : U → ℝ, IsNumericalUtility S v → IsNumericalUtility S v' →
        ∃ ω₀ ω₁ : ℝ, 0 < ω₀ ∧ ∀ w : U, v' w = ω₀ * v w + ω₁ := by
  by_cases hp : ∃ u0 u1 : U, u0 < u1
  · obtain ⟨u0, u1, h01⟩ := hp
    obtain ⟨h, ⟨_, _, hmono, hlin⟩, huniq⟩ := norm_core S hS u0 u1 h01
    refine ⟨⟨h, fun u w huw => hmono w u ((hS u w).1 huw), hlin⟩, ?_⟩
    have norm : ∀ v : U → ℝ, IsNumericalUtility S v →
        0 < v u1 - v u0 ∧ ∀ w, (v w - v u0) / (v u1 - v u0) = h w := by
      intro v hv
      have hd : 0 < v u1 - v u0 := sub_pos.2 (hv.1 u1 u0 ((hS _ _).2 h01))
      refine ⟨hd, fun w => ?_⟩
      have := huniq (fun w => (v w - v u0) / (v u1 - v u0)) (by simp)
        (div_self hd.ne') (fun γ u w _ => by
          rw [hv.2]; field_simp; ring)
      exact congrFun this w
    intro v v' hv hv'
    obtain ⟨hd, e⟩ := norm v hv
    obtain ⟨hd', e'⟩ := norm v' hv'
    refine ⟨(v' u1 - v' u0) / (v u1 - v u0), v' u0 - (v' u1 - v' u0) / (v u1 - v u0) * v u0,
      div_pos hd' hd, fun w => ?_⟩
    have := (e w).trans (e' w).symm
    field_simp at this ⊢
    linarith
  · push_neg at hp
    have heq : ∀ x y : U, x = y := fun x y => le_antisymm (hp y x) (hp x y)
    refine ⟨⟨fun _ => 0, fun u w huw => absurd ((hS u w).1 huw) (not_lt.2 (hp w u)),
      fun γ u w => by simp⟩, ?_⟩
    intro v v' _ _
    by_cases hn : Nonempty U
    · obtain ⟨x⟩ := hn
      refine ⟨1, v' x - v x, one_pos, fun w => ?_⟩
      rw [heq w x]; ring
    · exact ⟨1, 0, one_pos, fun w => absurd ⟨w⟩ hn⟩

end VNMCore

theorem normalized_utility_core {U : Type*} (S : UtilitySystem U) {uStar vStar : U}
    (hStar : S.lt uStar vStar) :
    ∃ h : U → ℝ,
      (h uStar = 0 ∧ h vStar = 1 ∧ (∀ u v : U, S.lt u v → h u < h v) ∧
        ∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v) ∧
      ∀ h₁ : U → ℝ, h₁ uStar = 0 → h₁ vStar = 1 →
        (∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h₁ (S.cmb γ u v) = (1 - (γ : ℝ)) * h₁ u + (γ : ℝ) * h₁ v) →
        h₁ = h := by
  letI := VNMAux.toLO S
  have hS : ∀ u v : U, S.gt u v ↔ v < u := fun u v => Iff.rfl
  obtain ⟨h, ⟨h0, h1, hmono, hlin⟩, huniq⟩ := VNMCore.norm_core S hS uStar vStar hStar
  exact ⟨h, ⟨h0, h1, fun u v huv => hmono u v huv, fun γ u v _ => hlin γ u v⟩,
    fun h₁ a b c => huniq h₁ a b (fun γ u v huv => c γ u v huv)⟩

theorem utility_existence_uniqueness_core {U : Type*} (S : UtilitySystem U) :
    (∃ v : U → ℝ, IsNumericalUtility S v) ∧
      ∀ v v' : U → ℝ, IsNumericalUtility S v → IsNumericalUtility S v' →
        ∃ ω₀ ω₁ : ℝ, 0 < ω₀ ∧ ∀ w : U, v' w = ω₀ * v w + ω₁ := by
  letI := VNMAux.toLO S
  exact VNMCore.goal_core S (fun u v => Iff.rfl)

end TheoryOfGames.Utility

open TheoryOfGames.Utility


theorem solution {U : Type*} (S : UtilitySystem U) {uStar vStar : U}
    (hStar : S.lt uStar vStar) :
    ∃ h : U → ℝ,
      (h uStar = 0 ∧ h vStar = 1 ∧ (∀ u v : U, S.lt u v → h u < h v) ∧
        ∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v) ∧
      ∀ h₁ : U → ℝ, h₁ uStar = 0 → h₁ vStar = 1 →
        (∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h₁ (S.cmb γ u v) = (1 - (γ : ℝ)) * h₁ u + (γ : ℝ) * h₁ v) →
        h₁ = h := by
  exact normalized_utility_core S hStar
