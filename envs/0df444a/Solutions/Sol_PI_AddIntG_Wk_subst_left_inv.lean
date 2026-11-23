-- Prove2me | solution 1 for PI.AddIntG.Wk.subst_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:22.145655+00:00
-- url     : https://prove2.me/submissions/ab163020-4b12-4152-b38e-e3ec10f53e70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
private theorem hasSubst_of_constantCoeff_eq_zero_additive_integral_groups {K : Type*} [Field K] {a : PowerSeries K}
    (ha : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a := by
  have ha2 : MvPowerSeries.constantCoeff a = 0 := ha
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero ha2
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [ha2]; exact IsNilpotent.zero)
private theorem hasSubst_of_mvConstantCoeff_eq_zero {K : Type*} [Field K] {σ : Type*} {b : MvPowerSeries σ K}
    (hb : MvPowerSeries.constantCoeff b = 0) : PowerSeries.HasSubst b := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hb
  | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hb]; exact IsNilpotent.zero)
private theorem subst_subst_eq_subst_subst_of_constantCoeff {K : Type*} [Field K] {σ : Type*} {a : PowerSeries K}
    {b : MvPowerSeries σ K} (ha : PowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (f : PowerSeries K) :
    PowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (PowerSeries.subst b a) f := by
  have ha' := hasSubst_of_constantCoeff_eq_zero_additive_integral_groups ha
  have hb' := hasSubst_of_mvConstantCoeff_eq_zero hb
  first
  | exact PowerSeries.subst_comp_subst_apply ha' hb' f
  | exact PowerSeries.subst_comp_subst_apply (R := K) ha' hb' f
  | exact congrFun (PowerSeries.subst_comp_subst ha' hb') f
  | simp [PowerSeries.subst_comp_subst_apply ha' hb']
private theorem subst_X_eq_self_of_constantCoeff_eq_zero {K : Type*} [Field K] {σ : Type*} {b : MvPowerSeries σ K}
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst b (PowerSeries.X : PowerSeries K) = b := by
  have hb' := hasSubst_of_mvConstantCoeff_eq_zero hb
  first
  | exact PowerSeries.subst_X hb'
  | simp [PowerSeries.subst_X hb']
private theorem coeff_pow_eq_zero_of_X_dvd_of_lt {K : Type*} [Field K] {y : PowerSeries K}
    (hy : PowerSeries.X ∣ y) {m d : ℕ} (h : m < d) : PowerSeries.coeff m (y ^ d) = 0 := by
  have hd : (PowerSeries.X : PowerSeries K) ^ d ∣ y ^ d := pow_dvd_pow_of_dvd hy d
  exact (PowerSeries.X_pow_dvd_iff.1 hd) m h
private theorem powerSeries_coeff_subst_eq_sum_range_coeff_mul {K : Type*} [Field K] {y : PowerSeries K}
    (hy : PowerSeries.constantCoeff y = 0) (l : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst y l) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d l * PowerSeries.coeff n (y ^ d) := by
  have hs := hasSubst_of_constantCoeff_eq_zero_additive_integral_groups hy
  have hX : PowerSeries.X ∣ y := PowerSeries.X_dvd_iff.2 hy
  have e : PowerSeries.coeff n (PowerSeries.subst y l) =
      ∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff n (y ^ d) := by
    first
    | exact PowerSeries.coeff_subst' hs l n
    | exact PowerSeries.coeff_subst hs l (Finsupp.single () n)
    | rw [PowerSeries.coeff_subst' hs]
    | simp only [PowerSeries.coeff_subst' hs]
  have hsupp : Function.support (fun d => PowerSeries.coeff d l • PowerSeries.coeff n (y ^ d)) ⊆
      ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero_of_X_dvd_of_lt hX (by omega), smul_zero])
  rw [e, finsum_eq_sum_of_support_subset _ hsupp]
  simp only [smul_eq_mul]
private theorem X_pow_add_two_dvd_pow_sub_pow_of_X_pow_dvd_sub {K : Type*} [Field K] {y z : PowerSeries K} {n d : ℕ}
    (hy : PowerSeries.X ∣ y) (hz : PowerSeries.X ∣ z) (hyz : PowerSeries.X ^ (n + 1) ∣ y - z)
    (hd : 2 ≤ d) : PowerSeries.X ^ (n + 2) ∣ y ^ d - z ^ d := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  have hab : (PowerSeries.X : PowerSeries K) ^ n ∣ a - b := by
    rw [pow_succ', ← mul_sub] at hyz
    exact (mul_dvd_mul_iff_left hX).1 hyz
  have h1 : a - b ∣ a ^ d - b ^ d := sub_dvd_pow_sub_pow a b d
  have h2 : (PowerSeries.X : PowerSeries K) ^ 2 ∣ PowerSeries.X ^ d := pow_dvd_pow _ hd
  have h3 : (PowerSeries.X : PowerSeries K) ^ (n + 2) =
      PowerSeries.X ^ 2 * PowerSeries.X ^ n := by ring
  rw [h3, mul_pow, mul_pow, ← mul_sub]
  exact mul_dvd_mul h2 (hab.trans h1)
private theorem eq_of_subst_eq_subst_of_coeff_one_eq_one {K : Type*} [Field K] {l y z : PowerSeries K}
    (hl1 : PowerSeries.coeff 1 l = 1) (hy : PowerSeries.constantCoeff y = 0)
    (hz : PowerSeries.constantCoeff z = 0)
    (h : PowerSeries.subst y l = PowerSeries.subst z l) : y = z := by
  have hXy : PowerSeries.X ∣ y := PowerSeries.X_dvd_iff.2 hy
  have hXz : PowerSeries.X ∣ z := PowerSeries.X_dvd_iff.2 hz
  have key : ∀ n : ℕ, (PowerSeries.X : PowerSeries K) ^ (n + 1) ∣ y - z := by
    intro n
    induction n with
    | zero =>
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, map_sub, hy, hz, sub_zero]
    | succ n ih =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      by_cases hm' : m < n + 1
      · exact PowerSeries.X_pow_dvd_iff.1 ih m hm'
      · have hmn : m = n + 1 := by omega
        subst hmn
        have e : PowerSeries.coeff (n + 1) (PowerSeries.subst y l) =
            PowerSeries.coeff (n + 1) (PowerSeries.subst z l) := by rw [h]
        rw [powerSeries_coeff_subst_eq_sum_range_coeff_mul hy, powerSeries_coeff_subst_eq_sum_range_coeff_mul hz] at e
        have h1 : 1 ∈ Finset.range (n + 1 + 1) := by simp
        have sy : ∑ d ∈ Finset.range (n + 1 + 1), PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d) =
            PowerSeries.coeff 1 l * PowerSeries.coeff (n + 1) (y ^ 1) +
              ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
                PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d) :=
          (Finset.add_sum_erase (Finset.range (n + 1 + 1))
            (fun d => PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d)) h1).symm
        have sz : ∑ d ∈ Finset.range (n + 1 + 1), PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d) =
            PowerSeries.coeff 1 l * PowerSeries.coeff (n + 1) (z ^ 1) +
              ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
                PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d) :=
          (Finset.add_sum_erase (Finset.range (n + 1 + 1))
            (fun d => PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d)) h1).symm
        have hrest : ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
              PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d) =
            ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
              PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_erase] at hd
          have hc : PowerSeries.coeff (n + 1) (y ^ d) = PowerSeries.coeff (n + 1) (z ^ d) := by
            rcases Nat.lt_or_ge d 2 with hd2 | hd2
            · have hd0 : d = 0 := by omega
              subst hd0
              simp
            · have hdv := X_pow_add_two_dvd_pow_sub_pow_of_X_pow_dvd_sub hXy hXz ih hd2
              have hzero := PowerSeries.X_pow_dvd_iff.1 hdv (n + 1) (by omega)
              rw [map_sub, sub_eq_zero] at hzero
              exact hzero
          rw [hc]
        rw [sy, sz, hrest, pow_one, pow_one, hl1, one_mul, one_mul] at e
        rw [map_sub, add_right_cancel e, sub_self]
  have hzero : y - z = 0 := by
    ext n
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 (key n) n (Nat.lt_succ_self n)
  exact sub_eq_zero.1 hzero
end PI.AddIntG.Wk
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hl1 : PowerSeries.coeff 1 l = 1) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hy0 : PowerSeries.constantCoeff (PowerSeries.subst l ex) = 0 := by
    first
    | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeries_coeff_subst_eq_sum_range_coeff_mul hl0]; simp [hex0])
    | (have h00 := powerSeries_coeff_subst_eq_sum_range_coeff_mul hl0 ex 0
       simp [hex0] at h00
       simpa using h00)
    | (obtain ⟨e, he⟩ := PowerSeries.X_dvd_iff.2 hex0
       rw [he, PowerSeries.subst_mul (hasSubst_of_constantCoeff_eq_zero_additive_integral_groups hl0), subst_X_eq_self_of_constantCoeff_eq_zero hl0, map_mul, hl0, zero_mul])
  have hXl : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l := by
    first
    | exact PowerSeries.subst_self l
    | (ext n
       rw [powerSeries_coeff_subst_eq_sum_range_coeff_mul PowerSeries.constantCoeff_X]
       simp [PowerSeries.coeff_X_pow])
  have heq : PowerSeries.subst (PowerSeries.subst l ex) l = PowerSeries.subst PowerSeries.X l := by
    rw [← subst_subst_eq_subst_subst_of_constantCoeff hex0 hl0 l, h, subst_X_eq_self_of_constantCoeff_eq_zero hl0, hXl]
  exact eq_of_subst_eq_subst_of_coeff_one_eq_one hl1 hy0 PowerSeries.constantCoeff_X heq
end PI.AddIntG.Wk
