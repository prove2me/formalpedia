-- Prove2me | solution 1 for PascalExtremes.padicVal_choose_le_of_common_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:28.945145+00:00
-- url     : https://prove2.me/submissions/c427ec03-c9ea-41c5-9ef8-0758fe5d4dba

module
public import Definitions.Def_PascalExtremes_Kummer
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_CarryBounds
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_not_carryAt_iff_mod_pow_le
public import Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p n k u t s x r : ℕ} (hp : p.Prime)
    (hnpos : 0 < n) (hkn : k ≤ n)
    (hu : u < p ^ t)
    (hn : n = u + p ^ t * s)
    (hk : k = u + p ^ t * x)
    (hxs : x ≤ s)
    (hs : s < p ^ (r + 1)) :
    padicValNat p (n.choose k) ≤ r := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpt : 0 < p ^ t := pow_pos hp.pos t
  have hsp : s + 1 ≤ p ^ (r + 1) := Nat.succ_le_iff.mpr hs
  have hnBound : n < p ^ (t + r + 1) := by
    rw [hn]
    calc
      u + p ^ t * s < p ^ t + p ^ t * s :=
        Nat.add_lt_add_right hu _
      _ = p ^ t * (s + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ p ^ t * p ^ (r + 1) :=
        Nat.mul_le_mul_left _ hsp
      _ = p ^ (t + r + 1) := by
        rw [← pow_add]
        congr 1
  have hlog : Nat.log p n < t + r + 1 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (Nat.ne_of_gt hnpos)).2 hnBound
  rw [padicVal_choose_eq_carryCount hkn hlog, carryCount]
  let F := (Finset.Ico 1 (t + r + 1)).filter fun i ↦ CarryAt p n k i
  have hsub : F ⊆ Finset.Ico (t + 1) (t + r + 1) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiRange := hi'.1
    have hiCarry := hi'.2
    simp only [Finset.mem_Ico] at hiRange ⊢
    refine ⟨?_, hiRange.2⟩
    by_contra hnot
    have hit : i ≤ t := by omega
    have hdvd : p ^ i ∣ p ^ t := Nat.pow_dvd_pow p hit
    have hnmod : n % p ^ i = u % p ^ i := by
      rw [hn, Nat.add_mod, Nat.mod_eq_zero_of_dvd
        (dvd_mul_of_dvd_left hdvd s), add_zero, Nat.mod_mod]
    have hkmod : k % p ^ i = u % p ^ i := by
      rw [hk, Nat.add_mod, Nat.mod_eq_zero_of_dvd
        (dvd_mul_of_dvd_left hdvd x), add_zero, Nat.mod_mod]
    have hno : ¬ CarryAt p n k i :=
      (not_carryAt_iff_mod_pow_le hp.pos hkn).2 (by simp [hnmod, hkmod])
    exact hno hiCarry
  have hcard := Finset.card_le_card hsub
  change F.card ≤ r
  calc
    F.card ≤ (Finset.Ico (t + 1) (t + r + 1)).card := hcard
    _ = r := by
      simp
end PascalExtremes
