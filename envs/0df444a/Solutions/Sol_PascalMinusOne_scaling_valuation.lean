-- Prove2me | solution 1 for PascalMinusOne.scaling_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:53.826507+00:00
-- url     : https://prove2.me/submissions/98b1b3bc-7d02-40d6-9852-9e287c90c12a

import Definitions.Def_PascalMinusOne_Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Scaling
import Theorems.Thm_PascalMinusOne_G_dvd_choose
import Theorems.Thm_PascalMinusOne_G_ne_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff


section
namespace PascalMinusOne
private theorem digitSum_pow_mul
    {p c n : ℕ} (hp : p.Prime) :
    (Nat.digits p (p ^ c * n)).sum = (Nat.digits p n).sum := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Nat.digits_base_pow_mul hp.one_lt (Nat.pos_of_ne_zero hn), List.sum_append]
    simp
private theorem padicVal_choose_pow_mul
    {p c n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    padicValNat p ((p ^ c * n).choose (p ^ c * k)) =
      padicValNat p (n.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hscaled : p ^ c * k ≤ p ^ c * n := Nat.mul_le_mul_left _ hkn
  have hs :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) hscaled
  have hu :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) hkn
  rw [← Nat.mul_sub_left_distrib,
    digitSum_pow_mul hp, digitSum_pow_mul hp, digitSum_pow_mul hp] at hs
  apply Nat.mul_left_cancel (Nat.sub_pos_of_lt hp.one_lt)
  exact hs.trans hu.symm
private theorem admissible_scale_iff
    {p c q N k : ℕ} (hp : p.Prime) :
    Admissible (p ^ c * N) (p ^ c * q) (p ^ c * k) ↔
      Admissible N q k := by
  have hpow : 0 < p ^ c := pow_pos hp.pos c
  constructor
  · rintro ⟨hkpos, hklt, hdiv⟩
    refine ⟨?_, (Nat.mul_lt_mul_left hpow).mp hklt, ?_⟩
    · by_contra h
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
      subst k
      simp at hkpos
    · rcases hdiv with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply Nat.mul_left_cancel hpow
      calc
        p ^ c * k = (p ^ c * q) * d := hd
        _ = p ^ c * (q * d) := by simp [Nat.mul_assoc]
  · rintro ⟨hkpos, hklt, hdiv⟩
    refine ⟨Nat.mul_pos hpow hkpos, (Nat.mul_lt_mul_left hpow).mpr hklt, ?_⟩
    exact Nat.mul_dvd_mul_left _ hdiv
private theorem exists_unscaled_of_admissible_scaled
    {p c q N K : ℕ} (hp : p.Prime)
    (hK : Admissible (p ^ c * N) (p ^ c * q) K) :
    ∃ k, Admissible N q k ∧ K = p ^ c * k := by
  rcases hK with ⟨hKpos, hKlt, hdiv⟩
  rcases hdiv with ⟨d, hd⟩
  let k := q * d
  have hKform : K = p ^ c * k := by
    calc
      K = (p ^ c * q) * d := hd
      _ = p ^ c * (q * d) := by simp [Nat.mul_assoc]
      _ = p ^ c * k := rfl
  have hpow : 0 < p ^ c := pow_pos hp.pos c
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hKform, hk0, mul_zero] at hKpos
    exact (Nat.not_lt_zero 0) hKpos
  have hklt : k < N := by
    rw [hKform] at hKlt
    exact (Nat.mul_lt_mul_left hpow).mp hKlt
  have hqk : q ∣ k := by
    refine ⟨d, ?_⟩
    rfl
  exact ⟨k, ⟨hkpos, hklt, hqk⟩, hKform⟩
private theorem admissibleIndices_zero (N : ℕ) :
    admissibleIndices N 0 = ∅ := by
  ext k
  simp only [mem_admissibleIndices_iff, Finset.notMem_empty, iff_false]
  rintro ⟨hkpos, _, hkdiv⟩
  have hk0 : k = 0 := by
    simpa using hkdiv
  exact (Nat.ne_of_gt hkpos) hk0
private theorem admissibleIndices_eq_empty_of_le
    {N m : ℕ} (hm : 0 < m) (hNm : N ≤ m) :
    admissibleIndices N m = ∅ := by
  ext k
  simp only [mem_admissibleIndices_iff, Finset.notMem_empty, iff_false]
  rintro ⟨hkpos, hklt, hdiv⟩
  have hmk : m ≤ k := Nat.le_of_dvd hkpos hdiv
  exact (Nat.not_lt_of_ge (hNm.trans hmk)) hklt
private theorem le_padicVal_G_iff
    {N m p r : ℕ} (hp : p.Prime) (hG : G N m ≠ 0) :
    r ≤ padicValNat p (G N m) ↔
      ∀ k, Admissible N m k → r ≤ padicValNat p (N.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hr k hk
    have hpG : p ^ r ∣ G N m :=
      (padicValNat_dvd_iff_le hG).2 hr
    have hGdvd : G N m ∣ N.choose k :=
      G_dvd_choose (mem_admissibleIndices_iff.mpr hk)
    have hchooseNe : N.choose k ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr hk.2.1.le
    exact
      (padicValNat_dvd_iff_le hchooseNe).1 (hpG.trans hGdvd)
  · intro h
    rw [← padicValNat_dvd_iff_le hG]
    rw [G, Finset.dvd_gcd_iff]
    intro k hk
    have hkadm : Admissible N m k :=
      mem_admissibleIndices_iff.mp hk
    have hchooseNe : N.choose k ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr hkadm.2.1.le
    exact
      (padicValNat_dvd_iff_le hchooseNe).2 (h k hkadm)
end PascalMinusOne
end

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {p c q N' : ℕ} (hp : p.Prime) :
    padicValNat p (G (p ^ c * N') (p ^ c * q)) =
      padicValNat p (G N' q) := by
  by_cases hq0 : q = 0
  · subst q
    simp [G, admissibleIndices_zero]
  by_cases hqN : q < N'
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hpow : 0 < p ^ c := pow_pos hp.pos c
    have hscaledqpos : 0 < p ^ c * q := Nat.mul_pos hpow hqpos
    have hscaledlt : p ^ c * q < p ^ c * N' :=
      (Nat.mul_lt_mul_left hpow).mpr hqN
    have hGscaled : G (p ^ c * N') (p ^ c * q) ≠ 0 :=
      G_ne_zero hscaledqpos hscaledlt
    have hGunscaled : G N' q ≠ 0 :=
      G_ne_zero hqpos hqN
    apply Nat.le_antisymm
    · refine (le_padicVal_G_iff (p := p) hp hGunscaled).2 ?_
      intro k hk
      have hkscaled :
          Admissible (p ^ c * N') (p ^ c * q) (p ^ c * k) :=
        (admissible_scale_iff hp).2 hk
      have hle :
          padicValNat p (G (p ^ c * N') (p ^ c * q)) ≤
            padicValNat p ((p ^ c * N').choose (p ^ c * k)) :=
        (le_padicVal_G_iff (p := p) hp hGscaled).1 (Nat.le_refl _) _ hkscaled
      rwa [padicVal_choose_pow_mul hp hk.2.1.le] at hle
    · refine (le_padicVal_G_iff (p := p) hp hGscaled).2 ?_
      intro K hK
      obtain ⟨k, hk, rfl⟩ :=
        exists_unscaled_of_admissible_scaled hp hK
      have hle :
          padicValNat p (G N' q) ≤ padicValNat p (N'.choose k) :=
        (le_padicVal_G_iff (p := p) hp hGunscaled).1 (Nat.le_refl _) _ hk
      rwa [padicVal_choose_pow_mul hp hk.2.1.le]
  · have hNq : N' ≤ q := Nat.le_of_not_gt hqN
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hpow : 0 < p ^ c := pow_pos hp.pos c
    have hunscaledEmpty : admissibleIndices N' q = ∅ :=
      admissibleIndices_eq_empty_of_le hqpos hNq
    have hscaledqpos : 0 < p ^ c * q := Nat.mul_pos hpow hqpos
    have hscaledNq : p ^ c * N' ≤ p ^ c * q :=
      Nat.mul_le_mul_left _ hNq
    have hscaledEmpty :
        admissibleIndices (p ^ c * N') (p ^ c * q) = ∅ :=
      admissibleIndices_eq_empty_of_le hscaledqpos hscaledNq
    simp [G, hunscaledEmpty, hscaledEmpty]
end PascalMinusOne
