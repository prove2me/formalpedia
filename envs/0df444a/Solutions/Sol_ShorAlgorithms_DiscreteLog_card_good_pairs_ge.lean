-- Prove2me | solution 1 for ShorAlgorithms.DiscreteLog.card_good_pairs_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:50:52.706867+00:00
-- url     : https://prove2.me/submissions/92279dd8-5f03-458d-8722-4261e86d49ee

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood
open ShorAlgorithms.DiscreteLog
namespace AShorLogCount

lemma good_d (p q r : ℕ) (hq : 0 < q) (c : Fin q)
    (hc : |(symmRes (q : ℤ) ((c : ℕ) * ((p : ℤ) - 1)) : ℝ)| ≤ (q : ℝ) / 12) :
    ∃ d : Fin q, IsGood p q r c d := by
  let t : ℝ := (r : ℝ) * (c : ℕ) - (r : ℝ) / ((p : ℝ) - 1) *
    (symmRes (q : ℤ) ((c : ℕ) * ((p : ℤ) - 1)) : ℝ)
  let z : ℤ := round (-t)
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hz0 := Int.emod_nonneg z (ne_of_gt hqz)
  have hzq := Int.emod_lt_of_pos z hqz
  let d : Fin q := ⟨(z % (q : ℤ)).toNat, by omega⟩
  refine ⟨d, ⟨?_, hc⟩⟩
  refine ⟨-(z / (q : ℤ)), ?_⟩
  have hdiv := Int.emod_add_ediv_mul z (q : ℤ)
  have hd : ((d : ℕ) : ℤ) = z % (q : ℤ) := Int.toNat_of_nonneg hz0
  have he : (d : ℕ) + (z / (q : ℤ) : ℤ) * (q : ℝ) = (z : ℝ) := by
    have hz := congrArg (fun x : ℤ => (x : ℝ)) hdiv
    push_cast at hz
    have hd' := congrArg (fun x : ℤ => (x : ℝ)) hd
    push_cast at hd'
    linarith
  have hab := abs_sub_round (-t)
  have ht : phaseT p q r c d - ((-(z / (q : ℤ)) : ℤ) : ℝ) * q = -(-t - z) := by
    simp only [phaseT, Int.cast_neg]
    dsimp [t]
    linarith
  rw [ht, abs_neg]
  exact hab

lemma bezout (N q : ℕ) :
    (N : ZMod q) * (Nat.gcdA N q : ℤ) = (Nat.gcd N q : ℕ) := by
  have h := congrArg (fun x : ℤ => (x : ZMod q)) (Nat.gcd_eq_gcd_ab N q)
  simpa using h.symm

lemma kernel_step (N q : ℕ) :
    (N : ZMod q) * ((q / Nat.gcd N q : ℕ) : ZMod q) = 0 := by
  have he : N * (q / Nat.gcd N q) = (N / Nat.gcd N q) * q := by
    calc N * (q / Nat.gcd N q)
      = ((N / Nat.gcd N q) * Nat.gcd N q) * (q / Nat.gcd N q) := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N q)]
      _ = (N / Nat.gcd N q) * q := by rw [mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right N q)]
  have h := congrArg (fun x : ℕ => (x : ZMod q)) he
  simpa only [Nat.cast_mul, ZMod.natCast_self, mul_zero] using h

lemma simple_residue (q v w : ℕ) (hq : 0 < q) (hw : w < q)
    (hh : 2 * w ≤ q) (he : (v : ZMod q) = w) : symmRes (q : ℤ) (v : ℤ) = w := by
  have hm : v % q = w := by
    have := congrArg ZMod.val he
    simpa [ZMod.val_natCast_of_lt hw] using this
  have hmz : (v : ℤ) % q = (w : ℤ) := by exact_mod_cast hm
  rw [symmRes, hmz, if_pos (by exact_mod_cast hh)]

lemma many_c (N q : ℕ) (hq : 0 < q) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Fin q), Function.Injective c ∧
      q ≤ 12 * Fintype.card ι ∧
      ∀ i, |(symmRes (q : ℤ) ((c i : ℕ) * (N : ℤ)) : ℝ)| ≤ (q : ℝ) / 12 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let g := Nat.gcd N q
  let h := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right N hq
  have hgh : g * h = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right N q)
  have hh : 0 < h := by nlinarith
  let ι := Fin (h / 12 + 1) × Fin g
  let f : ι → ZMod q := fun i => (Nat.gcdA N q : ℤ) * (i.1 : ℕ) + (h : ZMod q) * (i.2 : ℕ)
  let c : ι → Fin q := fun i => ⟨(f i).val, ZMod.val_lt _⟩
  have hik (i : ι) : (i.1 : ℕ) < h := by have := i.1.isLt; omega
  have him (i : ι) : (i.2 : ℕ) < g := i.2.isLt
  have hmul (i : ι) : (N : ZMod q) * f i = ((g * (i.1 : ℕ) : ℕ) : ZMod q) := by
    dsimp [f]
    rw [mul_add, ← mul_assoc, bezout, ← mul_assoc, kernel_step, zero_mul, add_zero]
    simp [Nat.cast_mul, g]
  have hi : Function.Injective f := by
    intro i j hij
    have hk := congrArg (fun x : ZMod q => (N : ZMod q) * x) hij
    rw [hmul, hmul] at hk
    have hk' := congrArg ZMod.val hk
    rw [ZMod.val_natCast_of_lt (by nlinarith [hik i]), ZMod.val_natCast_of_lt (by nlinarith [hik j])] at hk'
    have hki : i.1 = j.1 := Fin.ext (by nlinarith)
    have hm : ((h * (i.2 : ℕ) : ℕ) : ZMod q) = (h * (j.2 : ℕ) : ℕ) := by
      dsimp [f] at hij
      rw [hki] at hij
      simpa only [Nat.cast_mul] using add_left_cancel hij
    have hm' := congrArg ZMod.val hm
    rw [ZMod.val_natCast_of_lt (by nlinarith [him i]), ZMod.val_natCast_of_lt (by nlinarith [him j])] at hm'
    exact Prod.ext hki (Fin.ext (by nlinarith))
  refine ⟨ι, inferInstance, c, ?_, ?_, ?_⟩
  · intro i j hij
    apply hi
    have hv := congrArg Fin.val hij
    have hcast := congrArg (fun x : ℕ => (x : ZMod q)) hv
    simpa [c] using hcast
  · simp only [ι, Fintype.card_prod, Fintype.card_fin]
    have hdiv : h ≤ 12 * (h / 12 + 1) := by omega
    nlinarith
  · intro i
    have h12 : 12 * (i.1 : ℕ) ≤ h := by have := i.1.isLt; omega
    have hkq : g * (i.1 : ℕ) < q := by nlinarith [hik i]
    have hhalf : 2 * (g * (i.1 : ℕ)) ≤ q := by nlinarith
    have hv : (((c i : ℕ) * N : ℕ) : ZMod q) = (g * (i.1 : ℕ) : ℕ) := by
      simpa [c, mul_comm] using hmul i
    have hres := simple_residue q ((c i : ℕ) * N) (g * (i.1 : ℕ)) hq hkq hhalf hv
    have hres' : symmRes (q : ℤ) ((c i : ℕ) * (N : ℤ)) = (g * (i.1 : ℕ) : ℕ) := by simpa using hres
    rw [hres', Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    have hnat : 12 * (g * (i.1 : ℕ)) ≤ q := by nlinarith
    have hreal : (12 : ℝ) * (g * (i.1 : ℕ) : ℕ) ≤ q := by exact_mod_cast hnat
    linarith

open Classical in
lemma good_pairs_count (p q r : ℕ) (hp : 1 ≤ p) (hq : 0 < q) :
    q ≤ 12 * (Finset.univ.filter (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2)).card := by
  classical
  obtain ⟨ι, inst, c, hi, hcard, hc⟩ := many_c (p - 1) q hq
  letI := inst
  have hd (i : ι) : ∃ d : Fin q, IsGood p q r (c i) d := by
    apply good_d p q r hq (c i)
    simpa [Nat.cast_sub hp] using hc i
  choose d hd using hd
  let f : ι → Fin q × Fin q := fun i => (c i, d i)
  have hf : Function.Injective f := by
    intro i j he
    exact hi (congrArg Prod.fst he)
  have hle := Finset.card_le_card_of_injOn f
    (s := Finset.univ) (t := Finset.univ.filter (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2))
    (by intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd i⟩)
    (by intro i _ j _ he; exact hf he)
  simp only [Finset.card_univ] at hle
  omega
end AShorLogCount


open Classical in
theorem solution (p : ℕ) [hp : Fact p.Prime] (r : ℕ) (hr : r < p - 1)
    (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p) :
    (q : ℝ) ≤ 12 * ((Finset.univ.filter
      (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2)).card : ℝ)  := by
  exact_mod_cast AShorLogCount.good_pairs_count p q r hp.out.one_le (lt_trans hp.out.pos hpq)
