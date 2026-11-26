-- Prove2me | solution 1 for PascalExtremes.targetB_pure_power_witness_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:16.013678+00:00
-- url     : https://prove2.me/submissions/8c1d1f08-662d-4bfe-8acb-212f5ae938ff

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_not_carryAt_iff_mod_pow_le
public import Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
public import Theorems.Thm_PascalExtremes_padicVal_choose_pow_mul
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private theorem base_pure_power_choose_le_two
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    padicValNat p (((p ^ a + 1) * p).choose (p ^ a + 1)) ≤ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hkn : p ^ a + 1 ≤ (p ^ a + 1) * p := by
    have hmpos : 0 < p ^ a + 1 := by positivity
    nlinarith [hp.two_le]
  have hNform :
      (p ^ a + 1) * p = p ^ (a + 1) + p := by
    rw [pow_succ]
    ring
  have hNpos : 0 < (p ^ a + 1) * p := by
    exact Nat.mul_pos (by omega) hp.pos
  have hNlt : (p ^ a + 1) * p < p ^ (a + 2) := by
    rw [hNform]
    have hpLt : p < p ^ (a + 1) := by
      calc
        p = p ^ 1 := (pow_one p).symm
        _ < p ^ (a + 1) :=
          Nat.pow_lt_pow_right hp.one_lt (by omega)
    calc
      p ^ (a + 1) + p < p ^ (a + 1) + p ^ (a + 1) :=
        Nat.add_lt_add_left hpLt _
      _ = 2 * p ^ (a + 1) := by omega
      _ ≤ p * p ^ (a + 1) :=
        Nat.mul_le_mul_right _ hp.two_le
      _ = p ^ (a + 2) := by
        calc
          p * p ^ (a + 1) = p ^ (a + 1) * p := Nat.mul_comm _ _
          _ = p ^ ((a + 1) + 1) := (pow_succ p (a + 1)).symm
          _ = p ^ (a + 2) := by congr 1 <;> omega
  have hlog :
      Nat.log p ((p ^ a + 1) * p) < a + 2 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (Nat.ne_of_gt hNpos)).2 hNlt
  rw [padicVal_choose_eq_carryCount hkn hlog, carryCount]
  let C := (Finset.Ico 1 (a + 2)).filter
    fun i ↦ CarryAt p ((p ^ a + 1) * p) (p ^ a + 1) i
  have hsub : C ⊆ ({1, a + 1} : Finset ℕ) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiRange := Finset.mem_Ico.mp hi'.1
    have hcarry := hi'.2
    by_cases hi1 : i = 1
    · simp [hi1]
    by_cases hia : i = a + 1
    · simp [hia]
    have hi2 : 2 ≤ i := by omega
    have hiaLe : i ≤ a := by omega
    have hdivA : p ^ i ∣ p ^ a :=
      Nat.pow_dvd_pow p hiaLe
    have hpowigt1 : 1 < p ^ i := by
      calc
        1 < p := hp.one_lt
        _ ≤ p ^ i := by
          calc
            p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
    have hkmod : (p ^ a + 1) % p ^ i = 1 := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdivA, zero_add]
      simp [Nat.mod_eq_of_lt hpowigt1]
    have hdivTop : p ^ i ∣ p ^ (a + 1) :=
      Nat.pow_dvd_pow p (by omega)
    have hpLtPow : p < p ^ i := by
      calc
        p = p ^ 1 := (pow_one p).symm
        _ < p ^ i := Nat.pow_lt_pow_right hp.one_lt (by omega)
    have hnmod : ((p ^ a + 1) * p) % p ^ i = p := by
      rw [hNform, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdivTop, zero_add]
      simp [Nat.mod_eq_of_lt hpLtPow]
    have hno :
        ¬ CarryAt p ((p ^ a + 1) * p) (p ^ a + 1) i :=
      (not_carryAt_iff_mod_pow_le hp.pos hkn).2 (by
        rw [hkmod, hnmod]
        exact hp.one_le)
    exact False.elim (hno hcarry)
  have hcard := Finset.card_le_card hsub
  change C.card ≤ 2
  exact hcard.trans Finset.card_le_two
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a t : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (ht : 1 ≤ t) :
    padicValNat p
      (((p ^ a + 1) * p ^ t).choose
        ((p ^ a + 1) * p ^ (t - 1))) ≤ a := by
  have htEq : t = (t - 1) + 1 := by omega
  have hbase : p ^ a + 1 ≤ (p ^ a + 1) * p := by
    have hmpos : 0 < p ^ a + 1 := by positivity
    nlinarith [hp.two_le]
  have hscale :=
    padicVal_choose_pow_mul (p := p) (c := t - 1)
      (n := (p ^ a + 1) * p) (k := p ^ a + 1) hp hbase
  have hN :
      p ^ (t - 1) * ((p ^ a + 1) * p) =
        (p ^ a + 1) * p ^ t := by
    calc
      p ^ (t - 1) * ((p ^ a + 1) * p) =
          (p ^ a + 1) * (p ^ (t - 1) * p) := by ring
      _ = (p ^ a + 1) * p ^ ((t - 1) + 1) := by
        rw [pow_succ]
      _ = (p ^ a + 1) * p ^ t := by rw [← htEq]
  have hk :
      p ^ (t - 1) * (p ^ a + 1) =
        (p ^ a + 1) * p ^ (t - 1) := by ring
  rw [hN, hk] at hscale
  rw [hscale]
  exact (base_pure_power_choose_le_two hp ha).trans ha
end PascalExtremes
