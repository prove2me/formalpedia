-- Prove2me | solution 1 for SmallRatio.dedekindSum_eq_Asum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:21.710134+00:00
-- url     : https://prove2.me/submissions/4fb9bf50-1b34-430f-b927-52c4e8693710

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
public import Theorems.Thm_SmallRatio_sawtooth_natCast_div
public import Theorems.Thm_SmallRatio_sawtooth_zero
public import Theorems.Thm_SmallRatio_sum_mul_mod_perm

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (h k : ℕ) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k = (Asum h k : ℚ) / (k : ℚ) ^ 2 - ((k : ℚ) - 1) / 4 := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  -- each term, with the term `r = 0` corrected
  have hterm : ∀ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k) =
      ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2) - if r = 0 then 1 / 4 else 0 := by
    intro r hr
    rw [mem_range] at hr
    by_cases h0 : r = 0
    · subst h0; simp [sawtooth_zero]; norm_num
    · rw [if_neg h0]
      have hnr : ¬ k ∣ r := fun hd => h0 (Nat.eq_zero_of_dvd_of_lt hd hr)
      have hnhr : ¬ k ∣ h * r := by
        intro hd
        exact hnr ((Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc) hd))
      have e1 := sawtooth_natCast_div r k hk hnr
      have e2 := sawtooth_natCast_div (h * r) k hk hnhr
      rw [Nat.mod_eq_of_lt hr] at e1
      push_cast at e2
      rw [e1, e2, sub_zero]
  rw [dedekindSum, sum_congr rfl hterm, sum_sub_distrib, sum_ite_eq' (range k) 0 (fun _ => (1 : ℚ) / 4),
    if_pos (mem_range.2 hk)]
  -- expand
  have hsumr : ∑ r ∈ range k, (r : ℚ) = (k : ℚ) * (k - 1) / 2 := by
    have := Finset.sum_range_id_mul_two k
    have h2 : (∑ r ∈ range k, (r : ℚ)) * 2 = (k : ℚ) * (k - 1) := by
      have : ((∑ i ∈ range k, i : ℕ) : ℚ) * 2 = ((k * (k - 1) : ℕ) : ℚ) := by exact_mod_cast this
      push_cast at this
      rw [Nat.cast_sub (by omega)] at this
      simpa using this
    linarith
  have hsumt : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) = (k : ℚ) * (k - 1) / 2 := by
    rw [sum_mul_mod_perm h k hk hc (fun r => ((r : ℕ) : ℚ)), hsumr]
  have hA : (Asum h k : ℚ) = ∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ) := by
    unfold Asum; push_cast; rfl
  have hexp : ∑ r ∈ range k, ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2) =
      (∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ)) / k ^ 2
        - (∑ r ∈ range k, (r : ℚ)) / (2 * k) - (∑ r ∈ range k, ((h * r % k : ℕ) : ℚ)) / (2 * k)
        + (k : ℚ) / 4 := by
    rw [sum_div, sum_div, sum_div]
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    have : (k : ℚ) / 4 = ∑ _r ∈ range k, (1 : ℚ) / 4 := by
      rw [sum_const, card_range, nsmul_eq_mul]; ring
    rw [this, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    field_simp
    ring
  rw [hexp, hsumr, hsumt, ← hA]
  field_simp
  ring
end SmallRatio
