-- Prove2me | solution 1 for Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-20T11:29:31.179218+00:00
-- url     : https://prove2.me/submissions/f12e9d05-7af1-432f-b4c9-89d86ab994f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_3_lower_blocks
import Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_3_upper_blocks
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

private theorem survivorsSpec {lo hi c q : ℕ} :
    q ∈ GoldbachSieve.survivors lo hi c ↔
      max 2 lo ≤ q ∧ q ≤ hi ∧ ∀ r : ℕ, r.Prime → r ≤ c → r ∣ q → r = q := by
  unfold GoldbachSieve.survivors
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.card_eq_zero]
  constructor
  · rintro ⟨⟨hl, hh⟩, hz⟩
    refine ⟨hl, hh, fun r hp hc hd => ?_⟩
    by_contra hne
    have hm : r ∈ ((Finset.Icc 2 c).filter Nat.Prime).filter
        (fun r => r ∣ q ∧ r ≠ q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hc⟩, hp⟩, hd, hne⟩
    rw [hz] at hm
    exact Finset.notMem_empty _ hm
  · rintro ⟨hl, hh, h⟩
    refine ⟨⟨hl, hh⟩, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro r hr
    obtain ⟨hp, hd, hne⟩ := Finset.mem_filter.mp hr
    obtain ⟨hb, hprime⟩ := Finset.mem_filter.mp hp
    exact hne (h r hprime (Finset.mem_Icc.mp hb).2 hd)

private theorem certifiedWitness (n p q : ℕ)
    (hp : p.Prime) (hp2 : p ≤ 5569) (hq : q.Prime)
    (hl : max 2 (120000000000000 - 5569) ≤ q)
    (hh : q ≤ 130000000000000) (he : n = p + q) :
    ∃ p ∈ (Finset.Icc 2 5569).filter Nat.Prime,
      ∃ q ∈ GoldbachSieve.survivors (120000000000000 - 5569) 130000000000000 20000000,
        n = p + q := by
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hp2⟩, hp⟩,
    q, survivorsSpec.mpr ⟨hl, hh, ?_⟩, he⟩
  exact fun r hr _ hd => (Nat.prime_dvd_prime_iff_eq hr hq).mp hd

private theorem prime_2 : Nat.Prime 2 := by norm_num
private theorem prime_3 : Nat.Prime 3 := by norm_num
private theorem prime_11 : Nat.Prime 11 := by norm_num
private theorem prime_246209 : Nat.Prime 246209 := by norm_num
private theorem prime_19231 : Nat.Prime 19231 := by norm_num
private theorem prime_1846177 : Nat.Prime 1846177 := by
  apply lucas_primality 1846177 (10 : ZMod 1846177)
  · change (10 : ZMod 1846177) ^ 1846176 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (1846177 : ℕ) - 1 = 2 * (2 * (2 * (2 * (2 * (3 * (19231)))))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 923088 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 923088 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 923088 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 923088 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 923088 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_3).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 615392 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_19231).mp hd
      subst r
      change (10 : ZMod 1846177) ^ 96 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_7384709 : Nat.Prime 7384709 := by
  apply lucas_primality 7384709 (2 : ZMod 7384709)
  · change (2 : ZMod 7384709) ^ 7384708 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (7384709 : ℕ) - 1 = 2 * (2 * (1846177)) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 7384709) ^ 3692354 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 7384709) ^ 3692354 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_1846177).mp hd
      subst r
      change (2 : ZMod 7384709) ^ 4 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_119999999999947 : Nat.Prime 119999999999947 := by
  apply lucas_primality 119999999999947 (2 : ZMod 119999999999947)
  · change (2 : ZMod 119999999999947) ^ 119999999999946 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (119999999999947 : ℕ) - 1 = 2 * (3 * (11 * (246209 * (7384709)))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 119999999999947) ^ 59999999999973 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_3).mp hd
      subst r
      change (2 : ZMod 119999999999947) ^ 39999999999982 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_11).mp hd
      subst r
      change (2 : ZMod 119999999999947) ^ 10909090909086 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_246209).mp hd
      subst r
      change (2 : ZMod 119999999999947) ^ 487390794 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_7384709).mp hd
      subst r
      change (2 : ZMod 119999999999947) ^ 16249794 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_5 : Nat.Prime 5 := by norm_num
private theorem prime_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_17 : Nat.Prime 17 := by norm_num
private theorem prime_137 : Nat.Prime 137 := by norm_num
private theorem prime_112019 : Nat.Prime 112019 := by norm_num
private theorem prime_521784503 : Nat.Prime 521784503 := by
  apply lucas_primality 521784503 (5 : ZMod 521784503)
  · change (5 : ZMod 521784503) ^ 521784502 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (521784503 : ℕ) - 1 = 2 * (17 * (137 * (112019))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (5 : ZMod 521784503) ^ 260892251 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_17).mp hd
      subst r
      change (5 : ZMod 521784503) ^ 30693206 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_137).mp hd
      subst r
      change (5 : ZMod 521784503) ^ 3808646 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_112019).mp hd
      subst r
      change (5 : ZMod 521784503) ^ 4658 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_119999999999941 : Nat.Prime 119999999999941 := by
  apply lucas_primality 119999999999941 (2 : ZMod 119999999999941)
  · change (2 : ZMod 119999999999941) ^ 119999999999940 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (119999999999941 : ℕ) - 1 = 2 * (2 * (3 * (5 * (3833 * (521784503))))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 119999999999941) ^ 59999999999970 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 119999999999941) ^ 59999999999970 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_3).mp hd
      subst r
      change (2 : ZMod 119999999999941) ^ 39999999999980 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_5).mp hd
      subst r
      change (2 : ZMod 119999999999941) ^ 23999999999988 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_3833).mp hd
      subst r
      change (2 : ZMod 119999999999941) ^ 31307070180 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_521784503).mp hd
      subst r
      change (2 : ZMod 119999999999941) ^ 229980 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_769 : Nat.Prime 769 := by norm_num
private theorem prime_7 : Nat.Prime 7 := by norm_num
private theorem prime_107 : Nat.Prime 107 := by norm_num
private theorem prime_947 : Nat.Prime 947 := by norm_num
private theorem prime_1013291 : Nat.Prime 1013291 := by
  apply lucas_primality 1013291 (2 : ZMod 1013291)
  · change (2 : ZMod 1013291) ^ 1013290 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (1013291 : ℕ) - 1 = 2 * (5 * (107 * (947))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 1013291) ^ 506645 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_5).mp hd
      subst r
      change (2 : ZMod 1013291) ^ 202658 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_107).mp hd
      subst r
      change (2 : ZMod 1013291) ^ 9470 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_947).mp hd
      subst r
      change (2 : ZMod 1013291) ^ 1070 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_3546518501 : Nat.Prime 3546518501 := by
  apply lucas_primality 3546518501 (3 : ZMod 3546518501)
  · change (3 : ZMod 3546518501) ^ 3546518500 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (3546518501 : ℕ) - 1 = 2 * (2 * (5 * (5 * (5 * (7 * (1013291)))))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 1773259250 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 1773259250 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_5).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 709303700 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_5).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 709303700 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_5).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 709303700 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_7).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 506645500 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_1013291).mp hd
      subst r
      change (3 : ZMod 3546518501) ^ 3500 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_119999999999837 : Nat.Prime 119999999999837 := by
  apply lucas_primality 119999999999837 (2 : ZMod 119999999999837)
  · change (2 : ZMod 119999999999837) ^ 119999999999836 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (119999999999837 : ℕ) - 1 = 2 * (2 * (11 * (769 * (3546518501)))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 119999999999837) ^ 59999999999918 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (2 : ZMod 119999999999837) ^ 59999999999918 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_11).mp hd
      subst r
      change (2 : ZMod 119999999999837) ^ 10909090909076 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_769).mp hd
      subst r
      change (2 : ZMod 119999999999837) ^ 156046814044 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_3546518501).mp hd
      subst r
      change (2 : ZMod 119999999999837) ^ 33836 ≠ 1
      reduce_mod_char <;> decide
private theorem prime_6373 : Nat.Prime 6373 := by norm_num
private theorem prime_43801 : Nat.Prime 43801 := by norm_num
private theorem prime_214943 : Nat.Prime 214943 := by norm_num
private theorem prime_119999999999879 : Nat.Prime 119999999999879 := by
  apply lucas_primality 119999999999879 (17 : ZMod 119999999999879)
  · change (17 : ZMod 119999999999879) ^ 119999999999878 = 1
    reduce_mod_char
  · intro r hr hd
    have hfac : (119999999999879 : ℕ) - 1 = 2 * (6373 * (43801 * (214943))) := by norm_num
    rw [hfac] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with hd | hd | hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_2).mp hd
      subst r
      change (17 : ZMod 119999999999879) ^ 59999999999939 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_6373).mp hd
      subst r
      change (17 : ZMod 119999999999879) ^ 18829436686 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_43801).mp hd
      subst r
      change (17 : ZMod 119999999999879) ^ 2739663478 ≠ 1
      reduce_mod_char <;> decide
    · have he := (Nat.prime_dvd_prime_iff_eq hr prime_214943).mp hd
      subst r
      change (17 : ZMod 119999999999879) ^ 558287546 ≠ 1
      reduce_mod_char <;> decide
theorem solution (n : Nat)
    (hnlo : 120000000000000 <= n) (hnhi : n < 130000000000000)
    (hnEven : Even n) :
    Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
      (Exists fun q => And
        (Membership.mem (GoldbachSieve.survivors (120000000000000 - 5569)
          130000000000000 20000000) q) (n = p + q)) := by
  by_cases hs : n < 120000000000016
  · have hmod : n % 2 = 0 := Nat.even_iff.mp hnEven
    have hn : n = 120000000000000 ∨ n = 120000000000002 ∨ n = 120000000000004 ∨ n = 120000000000006 ∨ n = 120000000000008 ∨ n = 120000000000010 ∨ n = 120000000000012 ∨ n = 120000000000014 := by omega
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact certifiedWitness 120000000000000 53 119999999999947 (by norm_num) (by decide) prime_119999999999947
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000002 61 119999999999941 (by norm_num) (by decide) prime_119999999999941
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000004 167 119999999999837 (by norm_num) (by decide) prime_119999999999837
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000006 59 119999999999947 (by norm_num) (by decide) prime_119999999999947
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000008 61 119999999999947 (by norm_num) (by decide) prime_119999999999947
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000010 131 119999999999879 (by norm_num) (by decide) prime_119999999999879
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000012 71 119999999999941 (by norm_num) (by decide) prime_119999999999941
        (by decide) (by decide) (by decide)
    · exact certifiedWitness 120000000000014 67 119999999999947 (by norm_num) (by decide) prime_119999999999947
        (by decide) (by decide) (by decide)
  by_cases hm : n < 125000000000000
  · obtain ⟨p, hp, q, hq, he⟩ := Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3_lower_blocks n (by omega) (by omega) hnEven
    obtain ⟨hql, hqh, hf⟩ := survivorsSpec.mp hq
    refine ⟨p, hp, q, survivorsSpec.mpr ⟨?_, ?_, hf⟩, he⟩
    · omega
    · omega
  · obtain ⟨p, hp, q, hq, he⟩ := Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3_upper_blocks n (by omega) (by omega) hnEven
    obtain ⟨hql, hqh, hf⟩ := survivorsSpec.mp hq
    refine ⟨p, hp, q, survivorsSpec.mpr ⟨?_, ?_, hf⟩, he⟩
    · omega
    · omega
