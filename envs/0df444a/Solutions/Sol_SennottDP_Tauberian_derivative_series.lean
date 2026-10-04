-- Prove2me | solution 1 for SennottDP.Tauberian.derivative_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:40:42.37657+00:00
-- url     : https://prove2.me/submissions/b861f998-7777-4cce-958e-1cbf5ad02188

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

set_option autoImplicit false

lemma p63ac2000_radius_eq (v : ℕ → ℝ≥0) :
    SennottDP.Tauberian.radius (fun n => (v n : ℝ≥0∞)) =
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (v n : ℝ))).radius := by
  have h := (FormalMultilinearSeries.ofScalars ℝ (fun n => (v n : ℝ))).radius_inv_eq_limsup
  have hn : ∀ n, ‖FormalMultilinearSeries.ofScalars ℝ (fun n => (v n : ℝ)) n‖₊ = v n := by
    intro n
    ext
    simp
  simp only [hn] at h
  rw [SennottDP.Tauberian.radius,
    ← inv_inv (FormalMultilinearSeries.ofScalars ℝ (fun n => (v n : ℝ))).radius, h]
  congr 1
  congr 1
  funext n
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity), one_div]

lemma p63ac2000_norm_p (u : ℕ → ℝ≥0) (n : ℕ) :
    ‖FormalMultilinearSeries.ofScalars ℝ (fun n => (u n : ℝ)) n‖ = (u n : ℝ) := by
  simp

lemma p63ac2000_norm_q (u : ℕ → ℝ≥0) (n : ℕ) :
    ‖FormalMultilinearSeries.ofScalars ℝ
        (fun m => ((((m + 1 : ℕ) : ℝ≥0) * u (m + 1) : ℝ≥0) : ℝ)) n‖
      = ((n : ℝ) + 1) * (u (n + 1) : ℝ) := by
  rw [FormalMultilinearSeries.ofScalars_norm]
  push_cast
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma p63ac2000_radius_q (u : ℕ → ℝ≥0) :
    (FormalMultilinearSeries.ofScalars ℝ
        (fun m => ((((m + 1 : ℕ) : ℝ≥0) * u (m + 1) : ℝ≥0) : ℝ))).radius
      = (FormalMultilinearSeries.ofScalars ℝ (fun n => (u n : ℝ))).radius := by
  set p := FormalMultilinearSeries.ofScalars ℝ (fun n => (u n : ℝ)) with hp
  set q := FormalMultilinearSeries.ofScalars ℝ
        (fun m => ((((m + 1 : ℕ) : ℝ≥0) * u (m + 1) : ℝ≥0) : ℝ)) with hq
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    obtain ⟨C, hC, hb⟩ := q.norm_mul_pow_le_of_lt_radius hr
    refine p.le_radius_of_bound (max (u 0 : ℝ) ((r : ℝ) * C)) fun n => ?_
    rw [hp, p63ac2000_norm_p]
    rcases n with _ | m
    · simp
    · refine le_trans ?_ (le_max_right _ _)
      have h1 := hb m
      rw [hq, p63ac2000_norm_q] at h1
      have hr0 : (0 : ℝ) ≤ r := r.2
      have hu0 : (0 : ℝ) ≤ u (m + 1) := (u (m + 1)).2
      have hpow : (0 : ℝ) ≤ (r : ℝ) ^ m := pow_nonneg hr0 m
      have : (u (m + 1) : ℝ) * (r : ℝ) ^ m ≤ ((m : ℝ) + 1) * (u (m + 1) : ℝ) * (r : ℝ) ^ m := by
        have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        nlinarith [mul_nonneg hu0 hpow]
      calc (u (m + 1) : ℝ) * (r : ℝ) ^ (m + 1)
          = (r : ℝ) * ((u (m + 1) : ℝ) * (r : ℝ) ^ m) := by ring
        _ ≤ (r : ℝ) * C := by
          apply mul_le_mul_of_nonneg_left _ hr0
          linarith
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    obtain ⟨r', hrr', hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hrr : r < r' := by exact_mod_cast hrr'
    have hr'pos : (0 : ℝ) < r' := by
      have : (0 : ℝ≥0) < r' := lt_of_le_of_lt bot_le hrr
      exact_mod_cast this
    obtain ⟨C, hC, hb⟩ := p.norm_mul_pow_le_of_lt_radius hr'
    set ρ : ℝ := (r : ℝ) / r' with hρ
    have hρ0 : 0 ≤ ρ := div_nonneg r.2 hr'pos.le
    have hρ1 : ρ < 1 := (div_lt_one hr'pos).2 (by exact_mod_cast hrr)
    have hρn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
    have hs1 : Summable fun m : ℕ => (m : ℝ) ^ 1 * ρ ^ m :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hρn
    have hs2 : Summable fun m : ℕ => ρ ^ m := summable_geometric_of_lt_one hρ0 hρ1
    have hs : Summable fun m : ℕ => C / r' * (((m : ℝ) ^ 1 * ρ ^ m) + ρ ^ m) :=
      (hs1.add hs2).mul_left _
    apply q.le_radius_of_summable_norm
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) hs
    rw [hq, p63ac2000_norm_q]
    have h1 := hb (m + 1)
    rw [hp, p63ac2000_norm_p] at h1
    have hrm : (r : ℝ) ^ m = ρ ^ m * (r' : ℝ) ^ m := by
      rw [hρ, div_pow, div_mul_cancel₀]
      exact pow_ne_zero _ hr'pos.ne'
    have key : (u (m + 1) : ℝ) * (r : ℝ) ^ m ≤ C / r' * ρ ^ m := by
      rw [hrm]
      have hρm : 0 ≤ ρ ^ m := pow_nonneg hρ0 m
      have : (u (m + 1) : ℝ) * (r' : ℝ) ^ m ≤ C / r' := by
        rw [le_div_iff₀ hr'pos]
        calc (u (m + 1) : ℝ) * (r' : ℝ) ^ m * r' = (u (m + 1) : ℝ) * (r' : ℝ) ^ (m + 1) := by
              ring
          _ ≤ C := h1
      calc (u (m + 1) : ℝ) * (ρ ^ m * (r' : ℝ) ^ m)
          = ρ ^ m * ((u (m + 1) : ℝ) * (r' : ℝ) ^ m) := by ring
        _ ≤ ρ ^ m * (C / r') := mul_le_mul_of_nonneg_left this hρm
        _ = C / r' * ρ ^ m := by ring
    have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    calc ((m : ℝ) + 1) * (u (m + 1) : ℝ) * (r : ℝ) ^ m
        = ((m : ℝ) + 1) * ((u (m + 1) : ℝ) * (r : ℝ) ^ m) := by ring
      _ ≤ ((m : ℝ) + 1) * (C / r' * ρ ^ m) := mul_le_mul_of_nonneg_left key hm
      _ = C / r' * (((m : ℝ) ^ 1 * ρ ^ m) + ρ ^ m) := by ring

open scoped ENNReal NNReal Topology in open Filter in open SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0) (hR : 0 < radius (fun n => (u n : ℝ≥0∞))) :
    (∀ α : ℝ, 0 < α → ENNReal.ofReal α < radius (fun n => (u n : ℝ≥0∞)) →
        HasDerivAt (fun x : ℝ => ∑' n : ℕ, x ^ n * (u n : ℝ))
          (∑' n : ℕ, (n : ℝ) * α ^ (n - 1) * (u n : ℝ)) α) ∧
      radius (fun m => ((m + 1 : ℕ) : ℝ≥0∞) * (u (m + 1) : ℝ≥0∞))
        = radius (fun n => (u n : ℝ≥0∞)) := by
  have hq_eq : radius (fun m => ((m + 1 : ℕ) : ℝ≥0∞) * (u (m + 1) : ℝ≥0∞))
      = (FormalMultilinearSeries.ofScalars ℝ
        (fun m => ((((m + 1 : ℕ) : ℝ≥0) * u (m + 1) : ℝ≥0) : ℝ))).radius := by
    rw [← p63ac2000_radius_eq]
    push_cast
    rfl
  have hp_eq := p63ac2000_radius_eq u
  refine ⟨?_, by rw [hq_eq, hp_eq, p63ac2000_radius_q]⟩
  intro α hα hαR
  rw [hp_eq] at hαR
  obtain ⟨r, hαr, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hαR
  have hαr' : α < r := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal hα.le ENNReal.coe_ne_top).mp hαr
    simpa using this
  set q := FormalMultilinearSeries.ofScalars ℝ
        (fun m => ((((m + 1 : ℕ) : ℝ≥0) * u (m + 1) : ℝ≥0) : ℝ)) with hq
  have hrq : (r : ℝ≥0∞) < q.radius := by rw [hq, p63ac2000_radius_q]; exact hr
  have hsq := q.summable_norm_mul_pow hrq
  simp only [hq, p63ac2000_norm_q] at hsq
  have hbound : Summable fun n : ℕ => (n : ℝ) * (r : ℝ) ^ (n - 1) * (u n : ℝ) := by
    rw [← summable_nat_add_iff 1]
    refine hsq.congr fun m => ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hr0 : (0 : ℝ) ≤ r := r.2
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n x => x ^ n * (u n : ℝ))
    (g' := fun n x => (n : ℝ) * x ^ (n - 1) * (u n : ℝ))
    (t := Set.Ioo (-(r : ℝ)) r) (y₀ := α) hbound
    isOpen_Ioo isPreconnected_Ioo ?_ ?_ ?_ ?_ ?_
  · intro n y _
    exact (hasDerivAt_pow n y).mul_const _
  · intro n y hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
      NNReal.abs_eq]
    have hy' : |y| ≤ r := by
      rw [abs_le]; exact ⟨hy.1.le, hy.2.le⟩
    have : |y| ^ (n - 1) ≤ (r : ℝ) ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hu : (0 : ℝ) ≤ u n := (u n).2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hn) hu
  · exact ⟨by linarith, hαr'⟩
  · have hsp := (FormalMultilinearSeries.ofScalars ℝ (fun n => (u n : ℝ))).summable_norm_mul_pow hr
    simp only [p63ac2000_norm_p] at hsp
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsp
    have : α ^ n ≤ (r : ℝ) ^ n := pow_le_pow_left₀ hα.le hαr'.le n
    have hu : (0 : ℝ) ≤ u n := (u n).2
    nlinarith
  · exact ⟨by linarith, hαr'⟩
