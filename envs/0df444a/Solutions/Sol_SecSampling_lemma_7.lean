-- Prove2me | solution 1 for SecSampling.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:34:03.750255+00:00
-- url     : https://prove2.me/submissions/bcb0b33e-7ded-4a8a-ac5e-0b83cff8b89a

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace Aux_SecSampling_l7
open SecSampling

lemma take_idxOf_ne (a : Bool) : ∀ l : List Bool, ∀ x ∈ l.take (l.idxOf a), x ≠ a := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons b l ih =>
    intro x hx
    rw [List.idxOf_cons] at hx
    by_cases hb : b = a
    · subst hb; simp at hx
    · have : (b == a) = false := by simpa using hb
      rw [this] at hx
      simp only [cond_false, List.take_succ_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hb
      · exact ih x hx

lemma drop_lz_true (I : List Bool) (hI : false ∈ I) : ∀ x ∈ I.drop (lastZero I), x = true := by
  intro x hx
  unfold lastZero at hx
  rw [if_pos hI] at hx
  have h1 : x ∈ (I.drop (I.length - I.reverse.idxOf false)).reverse := List.mem_reverse.2 hx
  rw [← List.take_reverse] at h1
  have := take_idxOf_ne false I.reverse x h1
  simpa using this

lemma lz_pos (I : List Bool) (hI : false ∈ I) : 1 ≤ lastZero I := by
  unfold lastZero
  rw [if_pos hI]
  have := List.idxOf_lt_length_of_mem (List.mem_reverse.2 hI)
  rw [List.length_reverse] at this
  omega

lemma lz_le (I : List Bool) : lastZero I ≤ I.length := by
  unfold lastZero; split_ifs <;> omega

lemma win_one (q : LZStrategy) (hq : ∀ (m : ℕ) (h : List Bool), q m h = 0 ∨ q m h = 1)
    (I : List Bool) (hI : false ∈ I) (hw : winLZ q I = 1) :
    q (bitNorm I) (I.take (lastZero I)) = 1 ∧
      ∀ j ∈ Finset.Ico 1 (lastZero I), q (bitNorm I) (I.take j) = 0 := by
  unfold winLZ stopProbAt at hw
  rw [if_pos hI] at hw
  constructor
  · rcases hq (bitNorm I) (I.take (lastZero I)) with h | h
    · rw [h, zero_mul] at hw; exact absurd hw zero_ne_one
    · exact h
  · intro j hj
    rcases hq (bitNorm I) (I.take j) with h | h
    · exact h
    · exfalso
      have : ∏ j ∈ Finset.Ico 1 (lastZero I), (1 - q (bitNorm I) (I.take j)) = 0 :=
        Finset.prod_eq_zero hj (by rw [h, sub_self])
      rw [this, mul_zero] at hw
      exact zero_ne_one hw

end Aux_SecSampling_l7

open SecSampling Aux_SecSampling_l7 in
theorem solution (q : LZStrategy) (hq : ∀ (m : ℕ) (h : List Bool), q m h = 0 ∨ q m h = 1)
    (I₁ I₂ : List Bool) (h : Conflict I₁ I₂) :
    ¬ (winLZ q I₁ = 1 ∧ winLZ q I₂ = 1) := by
  rintro ⟨hw1, hw2⟩
  obtain ⟨hlen, hf1, hf2, hbn, hpre⟩ := h
  set r1 := lastZero I₁ with hr1
  set r2 := lastZero I₂ with hr2
  have hr1le := lz_le I₁
  -- counting: I₂ has a false after position r1
  have hc1 : bitNorm I₁ = bitNorm (I₁.take r1) + (I₁.length - r1) := by
    unfold bitNorm
    conv_lhs => rw [← List.take_append_drop r1 I₁]
    rw [List.count_append]
    congr 1
    rw [List.count_eq_length.2 (fun b hb => (drop_lz_true I₁ hf1 b hb).symm), List.length_drop]
  have hc2 : bitNorm I₂ = bitNorm (I₂.take r1) + (I₂.drop r1).count true := by
    unfold bitNorm
    conv_lhs => rw [← List.take_append_drop r1 I₂]
    rw [List.count_append]
  have hfalse : false ∈ I₂.drop r1 := by
    by_contra hno
    have hall : ∀ b ∈ I₂.drop r1, true = b := by
      intro b hb
      cases b
      · exact absurd hb hno
      · rfl
    have := List.count_eq_length.2 hall
    rw [List.length_drop] at this
    have hpre' : bitNorm (I₁.take r1) = bitNorm (I₂.take r1) := by rw [hpre]
    omega
  have hlt : r1 < r2 := by
    by_contra hge
    push_neg at hge
    have hmem : false ∈ I₂.drop r2 := by
      have e : I₂.drop r1 = (I₂.drop r2).drop (r1 - r2) := by
        rw [List.drop_drop]; congr 1; omega
      rw [e] at hfalse
      exact List.mem_of_mem_drop hfalse
    have := drop_lz_true I₂ hf2 false hmem
    exact Bool.false_ne_true this
  obtain ⟨hq1, _⟩ := win_one q hq I₁ hf1 hw1
  obtain ⟨_, hq2⟩ := win_one q hq I₂ hf2 hw2
  have := hq2 r1 (Finset.mem_Ico.2 ⟨lz_pos I₁ hf1, hlt⟩)
  rw [← hpre, ← hbn] at this
  rw [this] at hq1
  exact zero_ne_one hq1
