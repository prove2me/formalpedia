-- Prove2me | solution 1 for SennottDP.SEN.prop_7_1_1_average_cost_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:58:49.707604+00:00
-- url     : https://prove2.me/submissions/fee50f90-eb7e-4108-b677-b0a186f3d7c1

import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal
open Filter


namespace SennottDP.SEN

open Topology

lemma ratio711 (K : ℕ) : Tendsto (fun n : ℕ => ((n - K : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) atTop (𝓝 1) := by
  have hr : Tendsto (fun n : ℕ => (1 : ℝ) - (K : ℝ) / n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  rw [sub_zero] at hr
  have h2 := ENNReal.tendsto_ofReal hr
  rw [ENNReal.ofReal_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (K+1)] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_div_of_pos hnpos]
  congr 1
  rw [Nat.cast_sub (by omega)]
  field_simp

lemma s711_core {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (K : ℕ) (i : S) (θ : SennottDP.Discounted.Policy M) (hfin : horizonCost M θ K i < ⊤) :
    avgCost M θ i =
      limsup (fun n : ℕ => (∑ t ∈ Finset.Ico K n, SennottDP.Discounted.expCost M θ i t) / ((n - K : ℕ) : ℝ≥0∞))
        atTop := by
  set y := fun n : ℕ => (∑ t ∈ Finset.Ico K n, SennottDP.Discounted.expCost M θ i t) / ((n - K : ℕ) : ℝ≥0∞)
    with hy
  set r := fun n : ℕ => ((n - K : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) with hrdef
  set g := fun n : ℕ => horizonCost M θ K i / (n : ℝ≥0∞) with hg
  have hr : Tendsto r atTop (𝓝 1) := ratio711 K
  have hgt : Tendsto g atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hfin.ne)
      (a := horizonCost M θ K i)
    rw [mul_zero] at this
    simpa [hg, div_eq_mul_inv] using this
  have heq : (fun n : ℕ => horizonCost M θ n i / (n : ℝ≥0∞)) =ᶠ[atTop] g + y * r := by
    filter_upwards [eventually_ge_atTop (K+1)] with n hn
    have hD0 : ((n - K : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hDt : ((n - K : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    simp only [Pi.add_apply, Pi.mul_apply, hg, hy, hrdef, horizonCost]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : K ≤ n), ENNReal.add_div]
    congr 1
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc _ _ (n : ℝ≥0∞)⁻¹,
      ENNReal.inv_mul_cancel hD0 hDt, one_mul]
  unfold avgCost
  rw [limsup_congr heq, ENNReal.limsup_add_of_left_tendsto_zero hgt]
  apply le_antisymm
  · have := ENNReal.limsup_mul_le' (u := y) (v := r) (f := atTop)
      (Or.inr (by rw [hr.limsup_eq]; simp)) (Or.inr (by rw [hr.limsup_eq]; simp))
    rwa [hr.limsup_eq, mul_one] at this
  · have := ENNReal.le_limsup_mul (u := y) (v := r) (f := atTop)
    rwa [hr.liminf_eq, mul_one] at this

end SennottDP.SEN

open SennottDP.SEN


theorem solution {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (K : ℕ) (hK : 0 < K) (i : S) (θ : SennottDP.Discounted.Policy M) (hfin : horizonCost M θ K i < ⊤) :
    avgCost M θ i =
      limsup (fun n : ℕ => (∑ t ∈ Finset.Ico K n, SennottDP.Discounted.expCost M θ i t) / ((n - K : ℕ) : ℝ≥0∞))
        atTop := by
  exact s711_core M K i θ hfin
