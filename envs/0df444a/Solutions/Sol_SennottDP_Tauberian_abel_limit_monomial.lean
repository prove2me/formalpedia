-- Prove2me | solution 1 for SennottDP.Tauberian.abel_limit_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:21:45.254016+00:00
-- url     : https://prove2.me/submissions/9a42529b-ae5e-43b9-9bb5-83ad67a02772

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian.MonoAux

lemma one_sub_pow_eq (α : ℝ≥0) (hα : α ≤ 1) (k : ℕ) :
    (1 : ℝ≥0) - α ^ (k + 1) = (1 - α) * ∑ i ∈ Finset.range (k + 1), α ^ i := by
  apply NNReal.eq
  have h1 : α ^ (k + 1) ≤ 1 := pow_le_one₀ zero_le hα
  rw [NNReal.coe_sub h1, NNReal.coe_mul, NNReal.coe_sub hα, NNReal.coe_sum]
  push_cast
  rw [mul_neg_geom_sum]

end SennottDP.Tauberian.MonoAux

open scoped ENNReal NNReal Topology in open Filter SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (k : ℕ) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k)
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L / ((k : ℝ≥0∞) + 1))) := by
  set g : ℝ≥0 → ℝ≥0 := fun α => ∑ i ∈ Finset.range (k + 1), α ^ i with hg
  have hgc : Continuous g := by
    rw [hg]; fun_prop
  have hg1 : g 1 = (k : ℝ≥0) + 1 := by simp [hg]
  have hgpos : ∀ α, 1 ≤ g α := by
    intro α
    simp only [hg]
    rw [Finset.sum_range_succ']
    simp
  -- limit of the inverse factor
  have hA : Tendsto (fun α : ℝ≥0 => ((g α : ℝ≥0∞))⁻¹) (𝓝[<] (1 : ℝ≥0))
      (𝓝 (((k : ℝ≥0∞) + 1))⁻¹) := by
    have h0 : Tendsto (fun α : ℝ≥0 => ((g α : ℝ≥0∞))⁻¹) (𝓝 (1 : ℝ≥0))
        (𝓝 (((g 1 : ℝ≥0) : ℝ≥0∞))⁻¹) :=
      tendsto_inv_iff.2 ((ENNReal.continuous_coe.tendsto _).comp (hgc.tendsto 1))
    rw [hg1] at h0
    push_cast at h0
    exact h0.mono_left nhdsWithin_le_nhds
  -- limit of the Abel mean at α^(k+1)
  have hpow : Tendsto (fun α : ℝ≥0 => α ^ (k + 1)) (𝓝[<] (1 : ℝ≥0)) (𝓝[<] (1 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun α : ℝ≥0 => α ^ (k + 1)) (𝓝 (1 : ℝ≥0)) (𝓝 ((1 : ℝ≥0) ^ (k + 1))) :=
        ((continuous_pow (k + 1)).tendsto 1)
      rw [one_pow] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact pow_lt_one₀ zero_le (Set.mem_Iio.mp hα) (Nat.succ_ne_zero k)
  have hB := hlim.comp hpow
  have hmul := ENNReal.Tendsto.mul hA
    (Or.inl (ENNReal.inv_ne_zero.mpr (by simp))) hB
    (Or.inr (ENNReal.inv_ne_top.mpr (by simp)))
  have hlimeq : ((k : ℝ≥0∞) + 1)⁻¹ * L = L / ((k : ℝ≥0∞) + 1) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hlimeq] at hmul
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : α ≤ 1 := le_of_lt hα
  simp only [Function.comp_apply, abelMean, U]
  have hsum : (∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k)
      = ∑' n : ℕ, ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) ^ n * u n := by
    congr 1; funext n
    rw [ENNReal.coe_pow]; ring
  rw [hsum]
  have hfac : (1 : ℝ≥0∞) - ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) = (1 - (α : ℝ≥0∞)) * (g α : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub, SennottDP.Tauberian.MonoAux.one_sub_pow_eq α hα1 k,
      ENNReal.coe_mul, ENNReal.coe_sub]
  rw [hfac]
  have hne0 : (g α : ℝ≥0∞) ≠ 0 := by
    have := hgpos α
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le one_pos this))
  have hnetop : (g α : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc ((g α : ℝ≥0∞))⁻¹ * ((1 - (α : ℝ≥0∞)) * (g α : ℝ≥0∞) * ∑' n : ℕ, ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) ^ n * u n)
      = (((g α : ℝ≥0∞))⁻¹ * (g α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) ^ n * u n) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
