-- Prove2me | solution 1 for actuarial_c_cont_fractional_settlement_discount_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T17:18:32.103043+00:00
-- url     : https://prove2.me/submissions/571a19b1-ee52-4529-9b28-9c459787d076

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_annualSettlementPV
import Definitions.Def_actuarial_c_cont_fractionalSettlementPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances.Continuous

private theorem fractional_grid_exact (m h : ℕ) (delta t : ℝ)
    (hm : 0 < m) (ht : 0 ≤ t) (horizon : t < (h : ℝ)) :
    fractionalSettlementPV m h delta t =
      Real.exp (-delta * fractionalTime m (Nat.floor (t * (m : ℝ)) + 1)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htmpos : 0 ≤ t * (m : ℝ) := mul_nonneg ht hmpos.le
  let r : ℕ := Nat.floor (t * (m : ℝ))
  have htl : (r : ℝ) ≤ t * (m : ℝ) := Nat.floor_le htmpos
  have htu : t * (m : ℝ) < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrmem : r ∈ Finset.range (m * h) := by
    apply Finset.mem_range.mpr
    apply (Nat.floor_lt htmpos).mpr
    have hv := mul_lt_mul_of_pos_right horizon hmpos
    simpa only [Nat.cast_mul, mul_comm] using hv
  have hrlow : fractionalTime m r ≤ t := by
    unfold fractionalTime
    exact (div_le_iff₀ hmpos).mpr htl
  have hrhigh : t < fractionalTime m (r + 1) := by
    unfold fractionalTime
    apply (lt_div_iff₀ hmpos).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using htu
  unfold fractionalSettlementPV
  calc
    (∑ k ∈ Finset.range (m*h),
      if fractionalTime m k ≤ t ∧ t < fractionalTime m (k+1)
      then Real.exp (-delta * fractionalTime m (k+1)) else 0) =
      (if fractionalTime m r ≤ t ∧ t < fractionalTime m (r+1)
       then Real.exp (-delta * fractionalTime m (r+1)) else 0) := by
        apply Finset.sum_eq_single r
        · intro k hk hne
          have hnot : ¬ (fractionalTime m k ≤ t ∧ t < fractionalTime m (k+1)) := by
            intro hh
            have hkl : (k : ℝ) ≤ t * (m : ℝ) := by
              exact (div_le_iff₀ hmpos).mp hh.1
            have hku : t * (m : ℝ) < ((k+1:ℕ):ℝ) := by
              exact (lt_div_iff₀ hmpos).mp hh.2
            have hkr : k ≤ r := by
              by_contra hnkr
              have hrk : r + 1 ≤ k := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnkr)
              have hrkreal : (r : ℝ) + 1 ≤ (k : ℝ) := by
                exact_mod_cast hrk
              linarith
            have hrk : r < k + 1 := (Nat.floor_lt htmpos).mpr (by
              simpa only [Nat.cast_add, Nat.cast_one] using hku)
            have hle : r ≤ k := Nat.lt_succ_iff.mp hrk
            exact hne (Nat.le_antisymm hkr hle)
          simp [hnot]
        · intro hnomem
          exact (hnomem hrmem).elim
    _ = Real.exp (-delta * fractionalTime m (r+1)) := by
      simp [hrlow, hrhigh]

theorem solution (m h : ℕ) (delta t : ℝ)
    (hm : 0 < m) (hdelta : 0 ≤ delta)
    (ht : 0 ≤ t) (horizon : t < (h : ℝ)) :
    annualSettlementPV h delta t ≤ fractionalSettlementPV m h delta t ∧
      fractionalSettlementPV m h delta t ≤ deathPV (h : ℝ) delta t := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  let j : ℕ := Nat.floor t
  let r : ℕ := Nat.floor (t * (m : ℝ))
  have htj : t < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have htmpos : 0 ≤ t*(m:ℝ) := mul_nonneg ht hmpos.le
  have htr : t*(m:ℝ) < (r:ℝ) + 1 := Nat.lt_floor_add_one _
  have hrlow : (r:ℝ) ≤ t*(m:ℝ) := Nat.floor_le htmpos
  have hrfuture : t ≤ fractionalTime m (r+1) := by
    unfold fractionalTime
    apply le_of_lt
    apply (lt_div_iff₀ hmpos).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using htr
  have hcapnat : r + 1 ≤ m * (j+1) := by
    apply Nat.succ_le_iff.mpr
    apply (Nat.floor_lt htmpos).mpr
    have hv := mul_lt_mul_of_pos_right htj hmpos
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm] using hv
  have hcap : fractionalTime m (r+1) ≤ ((j+1:ℕ):ℝ) := by
    unfold fractionalTime
    apply (div_le_iff₀ hmpos).mpr
    have hreal : ((r+1:ℕ):ℝ) ≤ (m:ℝ)*((j+1:ℕ):ℝ) := by
      exact_mod_cast hcapnat
    simpa only [mul_comm] using hreal
  have hannual : annualSettlementPV h delta t =
      Real.exp (-delta * ((j+1:ℕ):ℝ)) := by
    have hgrid := fractional_grid_exact 1 h delta t (by decide) ht horizon
    have heq : annualSettlementPV h delta t =
        fractionalSettlementPV 1 h delta t := by
      simp [annualSettlementPV, fractionalSettlementPV, fractionalTime]
    rw [heq, hgrid]
    simp [fractionalTime, j]
  have hfractional := fractional_grid_exact m h delta t hm ht horizon
  have hdeath : deathPV (h : ℝ) delta t = Real.exp (-delta * t) := by
    simp [deathPV, ht, horizon]
  refine ⟨?_, ?_⟩
  · rw [hannual, hfractional]
    apply (Real.exp_le_exp).mpr
    have hd := mul_le_mul_of_nonneg_left hcap hdelta
    nlinarith
  · rw [hfractional, hdeath]
    apply (Real.exp_le_exp).mpr
    have hd := mul_le_mul_of_nonneg_left hrfuture hdelta
    nlinarith

