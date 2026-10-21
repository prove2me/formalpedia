-- Prove2me | solution 1 for UnknownProphet.NoSamples.coupling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:58:27.695724+00:00
-- url     : https://prove2.me/submissions/1f913ee0-0d31-45a3-8745-00e37bb859b0

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Telescoping product perturbation bound. -/
lemma coupling_prod_le {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (ha0 : ∀ j ∈ S, 0 ≤ a j) (ha1 : ∀ j ∈ S, a j ≤ 1)
    (hb0 : ∀ j ∈ S, 0 ≤ b j) (hb1 : ∀ j ∈ S, b j ≤ 1)
    (hab : ∀ j ∈ S, a j ≤ b j + ε) :
    ∏ j ∈ S, a j ≤ ∏ j ∈ S, b j + S.card * ε := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have ih' := ih (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb1 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hab j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.card_insert_of_notMem hk]
    have hA0 : 0 ≤ ∏ j ∈ S, a j :=
      Finset.prod_nonneg (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
    have hB0 : 0 ≤ ∏ j ∈ S, b j :=
      Finset.prod_nonneg (fun j hj => hb0 j (Finset.mem_insert_of_mem hj))
    have hB1 : ∏ j ∈ S, b j ≤ 1 :=
      Finset.prod_le_one (fun j hj => hb0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => hb1 j (Finset.mem_insert_of_mem hj))
    have hak0 := ha0 k (Finset.mem_insert_self k S)
    have hak1 := ha1 k (Finset.mem_insert_self k S)
    have hbk0 := hb0 k (Finset.mem_insert_self k S)
    have habk := hab k (Finset.mem_insert_self k S)
    push_cast
    calc a k * ∏ j ∈ S, a j ≤ a k * (∏ j ∈ S, b j + S.card * ε) :=
          mul_le_mul_of_nonneg_left ih' hak0
      _ = a k * ∏ j ∈ S, b j + a k * (S.card * ε) := by ring
      _ ≤ (b k + ε) * ∏ j ∈ S, b j + 1 * (S.card * ε) := by
          gcongr
      _ ≤ b k * ∏ j ∈ S, b j + ((S.card : ℝ) + 1) * ε := by
          nlinarith

theorem coupling_main (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (R : StoppingRule 0 n) (V : Set ℕ) (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h : ValueObliviousWith ε R V q)
    (s : Fin n → ℕ) (hs : ∀ j, s j ∈ V) (hinj : Function.Injective s) :
    pickMaxProb R (fun j => (s j : ℝ)) ≤
      pickMaxProb (hatRule q hq) (fun j => (s j : ℝ)) + n * ε := by
  classical
  set x : Fin n → ℝ := fun j => (s j : ℝ) with hx
  have xinj : Function.Injective x := fun a b hab => hinj (by simpa [hx] using hab)
  -- key: the value-oblivious bound at a record
  have hrec : ∀ (j : Fin n),
      (∀ l : Fin (j.val + 1), l ≠ Fin.last j.val →
        (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) l <
          (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) (Fin.last j.val)) →
      R.r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) ∈ Set.Ico (q j - ε) (q j + ε) := by
    intro j hj
    have := (h j).2 (Fin.elim0) (fun l => s (Fin.castLE (Nat.succ_le_of_lt j.isLt) l))
      (fun l => l.elim0) (fun l => hs _)
      (by
        rw [Fin.elim0_append]
        intro a b hab
        have := hinj hab
        have := congrArg Fin.val this
        simp at this
        exact Fin.ext (by simpa using this))
      (fun l => l.elim0)
      (by
        intro l hl
        have := hj l hl
        simp only [Function.comp_apply, hx] at this
        exact_mod_cast this)
    have e1 : (fun l : Fin 0 => ((Fin.elim0 l : ℕ) : ℝ)) = ![] := Subsingleton.elim _ _
    rw [e1] at this
    exact this
  -- per-index bound
  have hstop : ∀ i : Fin n, (∀ j, x j ≤ x i) →
      stopProb R ![] x i ≤ stopProb (hatRule q hq) ![] x i + n * ε := by
    intro i hi
    unfold stopProb
    set a : Fin n → ℝ := fun j => 1 - R.r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt))
    set b : Fin n → ℝ := fun j =>
      1 - (hatRule q hq).r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt))
    have hr01 : ∀ j : Fin n, R.r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) ∈
        Set.Icc (0:ℝ) 1 := fun j => R.r_mem _ _ _
    have hh01 : ∀ j : Fin n, (hatRule q hq).r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) ∈
        Set.Icc (0:ℝ) 1 := fun j => (hatRule q hq).r_mem _ _ _
    have hab : ∀ j ∈ Finset.Iio i, a j ≤ b j + ε := by
      intro j _
      simp only [a, b, hatRule]
      split_ifs with hc
      · have := hrec j hc
        linarith [this.1]
      · linarith [(hr01 j).1]
    have hP := coupling_prod_le (Finset.Iio i) a b ε hε.le
      (fun j _ => by simp only [a]; linarith [(hr01 j).2])
      (fun j _ => by simp only [a]; linarith [(hr01 j).1])
      (fun j _ => by simp only [b]; linarith [(hh01 j).2])
      (fun j _ => by simp only [b]; linarith [(hh01 j).1])
      hab
    have hirec : ∀ l : Fin (i.val + 1), l ≠ Fin.last i.val →
        (x ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) l <
          (x ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) (Fin.last i.val) := by
      intro l hl
      simp only [Function.comp_apply]
      apply lt_of_le_of_ne (hi _)
      intro heq
      have := xinj heq
      apply hl
      apply Fin.ext
      have := congrArg Fin.val this
      simp at this
      simp [this]
    have hri := hrec i hirec
    have hhat : (hatRule q hq).r i ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) = q i := by
      simp only [hatRule]
      rw [if_pos hirec]
    rw [hhat]
    have hA0 : 0 ≤ ∏ j ∈ Finset.Iio i, a j :=
      Finset.prod_nonneg (fun j _ => by simp only [a]; linarith [(hr01 j).2])
    have hA1 : ∏ j ∈ Finset.Iio i, a j ≤ 1 :=
      Finset.prod_le_one (fun j _ => by simp only [a]; linarith [(hr01 j).2])
        (fun j _ => by simp only [a]; linarith [(hr01 j).1])
    have hB0 : 0 ≤ ∏ j ∈ Finset.Iio i, b j :=
      Finset.prod_nonneg (fun j _ => by simp only [b]; linarith [(hh01 j).2])
    have hcard : ((Finset.Iio i).card : ℝ) + 1 ≤ n := by
      rw [Fin.card_Iio]
      have := i.isLt
      exact_mod_cast this
    have hq0 := (hq i).1
    have hq1 := (hq i).2
    have hr0 := (hr01 i).1
    calc (∏ j ∈ Finset.Iio i, a j) * R.r i ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt))
        ≤ (∏ j ∈ Finset.Iio i, a j) * (q i + ε) :=
          mul_le_mul_of_nonneg_left hri.2.le hA0
      _ ≤ (∏ j ∈ Finset.Iio i, a j) * q i + ε := by nlinarith
      _ ≤ (∏ j ∈ Finset.Iio i, b j + (Finset.Iio i).card * ε) * q i + ε := by
          gcongr
      _ ≤ (∏ j ∈ Finset.Iio i, b j) * q i + ((Finset.Iio i).card + 1) * ε := by
          have : ((Finset.Iio i).card : ℝ) * ε * q i ≤ (Finset.Iio i).card * ε := by
            have : (0:ℝ) ≤ (Finset.Iio i).card * ε := by positivity
            nlinarith
          nlinarith
      _ ≤ (∏ j ∈ Finset.Iio i, b j) * q i + n * ε := by gcongr
  -- uniqueness of argmax
  unfold pickMaxProb
  by_cases hex : ∃ i, ∀ j, x j ≤ x i
  · obtain ⟨i0, hi0⟩ := hex
    have huniq : ∀ i, (∀ j, x j ≤ x i) → i = i0 := by
      intro i hi
      exact xinj (le_antisymm (hi0 i) (hi i0)).symm |>.symm
    rw [Finset.sum_eq_single i0, Finset.sum_eq_single i0]
    · rw [if_pos hi0, if_pos hi0]
      exact hstop i0 hi0
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (huniq b hb')
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (huniq b hb')
    · simp
  · push Not at hex
    have h1 : ∀ i, (if ∀ j, x j ≤ x i then stopProb R ![] x i else 0) = 0 := by
      intro i
      rw [if_neg]
      intro hc
      obtain ⟨j, hj⟩ := hex i
      exact absurd (hc j) (not_le.mpr hj)
    have h2 : ∀ i, (if ∀ j, x j ≤ x i then stopProb (hatRule q hq) ![] x i else 0) = 0 := by
      intro i
      rw [if_neg]
      intro hc
      obtain ⟨j, hj⟩ := hex i
      exact absurd (hc j) (not_le.mpr hj)
    simp only [h1, h2, Finset.sum_const_zero, zero_add]
    positivity

end UnknownProphet.NoSamples

open UnknownProphet.NoSamples in
theorem solution (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (R : StoppingRule 0 n) (V : Set ℕ) (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h : ValueObliviousWith ε R V q)
    (s : Fin n → ℕ) (hs : ∀ j, s j ∈ V) (hinj : Function.Injective s) :
    pickMaxProb R (fun j => (s j : ℝ)) ≤
      pickMaxProb (hatRule q hq) (fun j => (s j : ℝ)) + n * ε :=
  coupling_main n ε hε R V q hq h s hs hinj
