-- Prove2me | solution 1 for Timetabling85.TwoPeriod.card_schedules_le_two
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:01:18.157849+00:00
-- url     : https://prove2.me/submissions/14b5d88a-677a-4e21-af5d-db30367c0d4d

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_CT4



namespace Timetabling85.TwoPeriod

open Classical

lemma eq_of_sum_le_one {ι : Type*} [Fintype ι] (f : ι → Bool)
    (h : ∑ a, (f a).toNat ≤ 1) {a b : ι} (ha : f a = true) (hb : f b = true) : a = b := by
  by_contra hne
  have h2 : ∑ c ∈ ({a, b} : Finset ι), (f c).toNat ≤ ∑ c, (f c).toNat :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne, ha, hb] at h2
  simp at h2
  omega

lemma sum_le_one_of_unique {ι : Type*} [Fintype ι] (f : ι → Bool)
    (h : ∀ a b, f a = true → f b = true → a = b) : ∑ a, (f a).toNat ≤ 1 := by
  by_cases hex : ∃ a, f a = true
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      have : f b = false := by
        by_contra hc
        exact hb (h b a (by simpa using hc) ha)
      simp [this]
    · simp
  · push_neg at hex
    simp [fun a => Bool.eq_false_iff.mpr (hex a)]

lemma toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

lemma sum_toNat_eq_zero_iff {ι : Type*} [Fintype ι] (f : ι → Bool) (h : ∑ a, (f a).toNat = 0) (a : ι) :
    f a = false := by
  have := (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ _)
  simpa using this

theorem card_schedules_core {m n p : ℕ} (I : CT4Data m n p) (j : Fin n)
    (hj : (Finset.univ.filter fun k => I.cbar j k = true).card ≤ 2) :
    (schedules I j).card ≤ 2 := by
  set K := Finset.univ.filter fun k => I.cbar j k = true with hK
  -- basic facts on a schedule
  have hout : ∀ y ∈ schedules I j, ∀ i k, k ∉ K → y i k = false := by
    intro y hy i k hk
    have hy' := (Finset.mem_filter.mp hy).2
    have h2 := hy'.2.1 k
    have hck : I.cbar j k = false := by
      by_contra hc
      exact hk (by simp [hK]; simpa using hc)
    rw [hck] at h2
    simp at h2
    exact sum_toNat_eq_zero_iff (fun i => y i k) (by simpa using h2) i
  have hcol : ∀ y ∈ schedules I j, ∀ k i i', y i k = true → y i' k = true → i = i' := by
    intro y hy k i i' h1 h2
    have hy' := (Finset.mem_filter.mp hy).2
    have h3 := hy'.2.1 k
    have : ∑ i, (y i k).toNat ≤ 1 := le_trans h3 (by cases I.cbar j k <;> simp)
    exact eq_of_sum_le_one (fun i => y i k) this h1 h2
  have hrow : ∀ y ∈ schedules I j, ∀ i, ∑ k, (y i k).toNat = I.rbar i j := by
    intro y hy i
    exact ((Finset.mem_filter.mp hy).2).1 i
  have hrowK : ∀ y ∈ schedules I j, ∀ i, ∑ k ∈ K, (y i k).toNat = I.rbar i j := by
    intro y hy i
    rw [← hrow y hy i]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp [hout y hy i k hk]
  by_cases hr : ∃ i0, I.rbar i0 j ≠ 0
  swap
  · -- all rows zero: unique schedule
    push_neg at hr
    have : (schedules I j).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy y' hy'
      funext i k
      have h1 := hrow y hy i
      have h2 := hrow y' hy' i
      rw [hr i] at h1 h2
      have a := sum_toNat_eq_zero_iff (fun k => y i k) h1 k
      have b := sum_toNat_eq_zero_iff (fun k => y' i k) h2 k
      rw [a, b]
    omega
  obtain ⟨i0, hi0⟩ := hr
  by_cases hK1 : K.card ≤ 1
  · have : (schedules I j).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy y' hy'
      funext i k
      by_cases hk : k ∈ K
      · have e : ∀ z ∈ schedules I j, (z i k).toNat = I.rbar i j := by
          intro z hz
          rw [← hrowK z hz i]
          rw [Finset.sum_eq_single k]
          · intro b hb hbk
            exact absurd (Finset.card_le_one.mp hK1 b hb k hk) hbk
          · intro h; exact absurd hk h
        exact toNat_inj ((e y hy).trans (e y' hy').symm)
      · rw [hout y hy i k hk, hout y' hy' i k hk]
    omega
  · have hK2 : K.card = 2 := by omega
    obtain ⟨k1, k2, hne, hKe⟩ := Finset.card_eq_two.mp hK2
    have hrow2 : ∀ y ∈ schedules I j, ∀ i, (y i k1).toNat + (y i k2).toNat = I.rbar i j := by
      intro y hy i
      have := hrowK y hy i
      rw [hKe, Finset.sum_pair hne] at this
      exact this
    -- injection y ↦ y i0 k1
    have hinj : ∀ y ∈ schedules I j, ∀ y' ∈ schedules I j, y i0 k1 = y' i0 k1 → y = y' := by
      intro y hy y' hy' hb
      have colk1 : ∀ i, y i k1 = y' i k1 := by
        intro i
        cases hb' : y i0 k1 with
        | true =>
          by_cases hii : i = i0
          · subst hii; rw [hb'] at hb; rw [hb', ← hb]
          · have a : y i k1 = false := by
              by_contra hc
              exact hii (hcol y hy k1 i i0 (by simpa using hc) hb')
            have b : y' i k1 = false := by
              by_contra hc
              exact hii (hcol y' hy' k1 i i0 (by simpa using hc) (hb ▸ hb'))
            rw [a, b]
        | false =>
          have hb2 : y' i0 k1 = false := hb ▸ hb'
          have a0 : y i0 k2 = true := by
            have := hrow2 y hy i0
            rw [hb'] at this
            cases h : y i0 k2 <;> simp_all
          have b0 : y' i0 k2 = true := by
            have := hrow2 y' hy' i0
            rw [hb2] at this
            cases h : y' i0 k2 <;> simp_all
          by_cases hii : i = i0
          · subst hii; rw [hb', hb2]
          · have a : y i k2 = false := by
              by_contra hc
              exact hii (hcol y hy k2 i i0 (by simpa using hc) a0)
            have b : y' i k2 = false := by
              by_contra hc
              exact hii (hcol y' hy' k2 i i0 (by simpa using hc) b0)
            have e1 := hrow2 y hy i
            have e2 := hrow2 y' hy' i
            rw [a] at e1; rw [b] at e2
            have : (y i k1).toNat = (y' i k1).toNat := by simp at e1 e2; omega
            exact toNat_inj this
      have colk2 : ∀ i, y i k2 = y' i k2 := by
        intro i
        have e1 := hrow2 y hy i
        have e2 := hrow2 y' hy' i
        rw [colk1 i] at e1
        have : (y i k2).toNat = (y' i k2).toNat := by omega
        exact toNat_inj this
      funext i k
      by_cases hk : k ∈ K
      · rw [hKe] at hk
        simp at hk
        rcases hk with rfl | rfl
        · exact colk1 i
        · exact colk2 i
      · rw [hout y hy i k hk, hout y' hy' i k hk]
    calc (schedules I j).card ≤ (Finset.univ : Finset Bool).card := by
          apply Finset.card_le_card_of_injOn (fun y => y i0 k1)
          · intro y _; simp
          · intro y hy y' hy' h
            exact hinj y hy y' hy' h
      _ = 2 := by simp

end Timetabling85.TwoPeriod

open Timetabling85.TwoPeriod


theorem solution {m n p : ℕ} (I : CT4Data m n p) (j : Fin n)
    (hj : (Finset.univ.filter fun k => I.cbar j k = true).card ≤ 2) :
    (schedules I j).card ≤ 2 := by
  exact card_schedules_core I j hj
