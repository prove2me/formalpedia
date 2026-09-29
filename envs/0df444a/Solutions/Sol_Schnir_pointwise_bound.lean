-- Prove2me | solution 1 for Schnir.pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:08.718664+00:00
-- url     : https://prove2.me/submissions/d7d28bf5-90b3-49f5-9634-abcc94e4d830

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_sieve_ineq
import Theorems.Thm_Schnir_G_lower

open Finset Real

namespace Schnir

/-- Pairs counted by `r s` either have a small prime or are counted by `S s z`. -/
theorem pw_r_le_S (s : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (r s : ℝ) ≤ S s z + 2 * z := by
  have hsub : (Finset.range (s + 1)).filter
      (fun p => p.Prime ∧ p ≠ 2 ∧ (s - p).Prime ∧ s - p ≠ 2) ⊆
      (Finset.Icc 1 ⌊z⌋₊ ∪ (Finset.Icc 1 ⌊z⌋₊).image (fun q => s - q)) ∪
      (Finset.Icc 1 s).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hps, hpp, -, hqp, -⟩ := hp
    have hp1 := hpp.one_lt
    have hq1 := hqp.one_lt
    by_cases h1 : p ≤ ⌊z⌋₊
    · simp only [Finset.mem_union, Finset.mem_Icc]; left; left; omega
    by_cases h2 : s - p ≤ ⌊z⌋₊
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]; left; right
      exact ⟨s - p, ⟨by omega, h2⟩, by omega⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    right
    refine ⟨⟨by omega, by omega⟩, fun q hq hqpr hdvd => ?_⟩
    rcases (Nat.Prime.dvd_mul hqpr).1 hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqpr hpp).1 h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hqpr hqp).1 h; omega
  set T := (Finset.Icc 1 s).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a)) with hT
  have hcard := Finset.card_le_card hsub
  have h3 : ((Finset.Icc 1 ⌊z⌋₊ ∪ (Finset.Icc 1 ⌊z⌋₊).image (fun q => s - q)) ∪ T).card
      ≤ ⌊z⌋₊ + ⌊z⌋₊ + T.card := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans ?_
    have := (Finset.card_image_le (s := Finset.Icc 1 ⌊z⌋₊) (f := fun q => s - q))
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this ⊢
    omega
  have h4 := hcard.trans h3
  have h5 : (r s : ℝ) ≤ (⌊z⌋₊ : ℝ) + ⌊z⌋₊ + S s z := by
    unfold r S; exact_mod_cast h4
  have h6 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
  linarith

/-- `C s ≥ 3` for even `s`. -/
theorem pw_C_ge_three (s : ℕ) (hs : Even s) (hs0 : 0 < s) : 3 ≤ C s := by
  unfold C
  have h2 : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hs, by omega⟩
  rw [← Finset.mul_prod_erase _ _ h2]
  have hrest : (1 : ℝ) ≤ ∏ p ∈ s.primeFactors.erase 2, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    calc (1 : ℝ) = ∏ p ∈ s.primeFactors.erase 2, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intros; norm_num
        · intro p _
          have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
          linarith
  norm_num
  linarith

/-- `log L ≤ L / 100` for `L ≥ 1000`. -/
theorem pw_log_le (L : ℝ) (hL : 1000 ≤ L) : Real.log L ≤ L / 100 := by
  have h7 : Real.log 1000 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (1000 : ℝ) < 2.7182818283 ^ 7 := by norm_num
      _ < Real.exp 1 ^ 7 := by gcongr
  have h1 : Real.log (L / 1000) ≤ L / 1000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  linarith

theorem pointwise_bound (s : ℕ) (hs : Even s) (hbig : Real.exp 1000 ≤ s) :
    (r s : ℝ) ≤ 9 * C s * s / (Real.log s) ^ 2 := by
  have hs1 : (1001 : ℝ) ≤ s := by
    have := Real.add_one_le_exp 1000; linarith
  have hs0 : 0 < s := by exact_mod_cast (show (0:ℝ) < s by linarith)
  have hspos : (0 : ℝ) < s := by linarith
  set L := Real.log s with hLdef
  have hL : 1000 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 1000) hbig
    rwa [Real.log_exp] at this
  have hLpos : 0 < L := by linarith
  have hlogL := pw_log_le L hL
  have hlogL' : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hLpos]
    have := Real.exp_one_lt_d9; linarith
  set z := √(s : ℝ) / L ^ 2 with hzdef
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.2 hspos
  have hzpos : 0 < z := by positivity
  have hlogz : Real.log z = L / 2 - 2 * Real.log L := by
    rw [hzdef, Real.log_div hsq.ne' (by positivity), Real.log_sqrt hspos.le, Real.log_pow]
    push_cast; ring
  have hlz1 : 12 / 25 * L ≤ Real.log z := by rw [hlogz]; linarith
  have hlz2 : 1 + Real.log z ≤ L / 2 := by rw [hlogz]; linarith
  have hz1 : 1 < z := by
    have : 0 < Real.log z := by linarith
    exact (Real.log_pos_iff hzpos.le).1 this
  have hC := pw_C_ge_three s hs hs0
  have hSi := sieve_ineq s hs hs0 z hz1
  have hG := G_lower s hs hs0 z hz1
  have hrS := pw_r_le_S s z hzpos.le
  have hlzpos : 0 < Real.log z := by linarith
  have hGpos : 0 < G s z := lt_of_lt_of_le (by positivity) hG
  -- s / G ≤ 2 C s / (log z)^2 ≤ 625/72 * C s / L^2
  have hA : (s : ℝ) / G s z ≤ 625 / 72 * C s * s / L ^ 2 := by
    rw [div_le_div_iff₀ hGpos (by positivity)]
    have h1 : (Real.log z) ^ 2 ≤ 2 * C s * G s z := by
      rw [div_le_iff₀ (by positivity)] at hG; linarith
    have h2 : 144 / 625 * L ^ 2 ≤ (Real.log z) ^ 2 := by nlinarith
    have : L ^ 2 ≤ 625 / 72 * C s * G s z := by nlinarith
    nlinarith
  have hzsq : z ^ 2 = s / L ^ 4 := by
    rw [hzdef, div_pow, Real.sq_sqrt hspos.le]; ring
  have hB : z ^ 2 * (1 + Real.log z) ^ 2 ≤ s / (4 * L ^ 2) := by
    rw [hzsq]
    have h0 : 0 ≤ 1 + Real.log z := by linarith
    have : (1 + Real.log z) ^ 2 ≤ (L / 2) ^ 2 := by gcongr
    calc (s : ℝ) / L ^ 4 * (1 + Real.log z) ^ 2 ≤ s / L ^ 4 * (L / 2) ^ 2 := by gcongr
      _ = s / (4 * L ^ 2) := by field_simp; ring
  have h8 : 8 ≤ √(s : ℝ) := by
    rw [show (8 : ℝ) = √64 by rw [show (64:ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hD : 2 * z ≤ s / (4 * L ^ 2) := by
    rw [← sub_nonneg]
    have hss : (s : ℝ) = √(s:ℝ) * √(s:ℝ) := (Real.mul_self_sqrt hspos.le).symm
    have : (s : ℝ) / (4 * L ^ 2) - 2 * z = √(s:ℝ) * (√(s:ℝ) - 8) / (4 * L ^ 2) := by
      rw [hzdef]; nth_rewrite 1 [hss]; field_simp; ring
    rw [this]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg hsq.le; linarith
  have hfin : (625 / 72 * C s * s / L ^ 2) + s / (4 * L ^ 2) + s / (4 * L ^ 2)
      ≤ 9 * C s * s / L ^ 2 := by
    rw [← sub_nonneg]
    have : 9 * C s * s / L ^ 2 - ((625 / 72 * C s * s / L ^ 2) + s / (4 * L ^ 2)
      + s / (4 * L ^ 2)) = (23 / 72 * C s - 1 / 2) * s / L ^ 2 := by field_simp; ring
    rw [this]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg _ hspos.le
    linarith
  linarith
end Schnir

open Schnir in
theorem solution (s : ℕ) (hs : Even s) (hbig : Real.exp 1000 ≤ s) :
    (r s : ℝ) ≤ 9 * C s * s / (Real.log s) ^ 2 :=
  Schnir.pointwise_bound s hs hbig
