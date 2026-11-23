-- Prove2me | solution 1 for PlatonicJEPA.next_token_prediction_margin_limit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:16:43.770616+00:00
-- url     : https://prove2.me/submissions/71b120ae-763b-4022-b270-f0c72737490a

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology
namespace PlatonicJEPA


theorem next_token_prediction_margin_limit {V : Type*} [Fintype V] [Nonempty V] {k : ℕ}
    (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) :
    Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0)
      (𝓝 (⨆ v, ∑ i, h i * w v i)) ∧
    Tendsto (fun t : ℝ => t * ntpLoss w (fun i => h i / t) y) (𝓝[>] 0)
      (𝓝 ((⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i)) ∧
    0 ≤ (⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i ∧
    ((⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i = 0 ↔ ∀ v, ∑ i, h i * w v i ≤ ∑ i, h i * w y i) := by
  set s : V → ℝ := fun v => ∑ i, h i * w v i with hs
  set M : ℝ := ⨆ v, s v with hM
  have hle : ∀ v, s v ≤ M := fun v => le_ciSup (Set.finite_range s).bddAbove v
  obtain ⟨v0, hv0⟩ : ∃ v0, s v0 = M := by
    obtain ⟨v0, hv⟩ := exists_eq_ciSup_of_finite (f := s)
    exact ⟨v0, hv⟩
  have hinner : ∀ (t : ℝ) (v : V), (∑ i, h i / t * w v i) = s v / t := by
    intro t v
    simp only [hs, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlow : ∀ t : ℝ, 0 < t → M ≤ t * ntpAntiCollapse w (fun i => h i / t) := by
    intro t ht
    unfold ntpAntiCollapse
    simp only [hinner]
    have h1 : Real.exp (M / t) ≤ ∑ v, Real.exp (s v / t) := by
      rw [← hv0]
      exact Finset.single_le_sum (f := fun v => Real.exp (s v / t)) (fun v _ => (Real.exp_pos _).le)
        (Finset.mem_univ v0)
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    have := mul_le_mul_of_nonneg_left h2 ht.le
    rwa [mul_div_cancel₀ _ ht.ne'] at this
  have hupp : ∀ t : ℝ, 0 < t →
      t * ntpAntiCollapse w (fun i => h i / t) ≤ M + t * Real.log (Fintype.card V) := by
    intro t ht
    unfold ntpAntiCollapse
    simp only [hinner]
    have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have h1 : ∑ v, Real.exp (s v / t) ≤ (Fintype.card V : ℝ) * Real.exp (M / t) := by
      calc ∑ v, Real.exp (s v / t) ≤ ∑ _v : V, Real.exp (M / t) :=
            Finset.sum_le_sum fun v _ => Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hle v) ht.le)
        _ = _ := by simp
    have hpos : 0 < ∑ v, Real.exp (s v / t) :=
      Finset.sum_pos (fun v _ => Real.exp_pos _) Finset.univ_nonempty
    have h2 := Real.log_le_log hpos h1
    rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    have := mul_le_mul_of_nonneg_left h2 ht.le
    rw [mul_add, mul_div_cancel₀ _ ht.ne'] at this
    linarith
  have hT1 : Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0) (𝓝 M) := by
    have hup : Tendsto (fun t : ℝ => M + t * Real.log (Fintype.card V)) (𝓝[>] 0) (𝓝 M) := by
      have : Tendsto (fun t : ℝ => M + t * Real.log (Fintype.card V)) (𝓝 0)
          (𝓝 (M + 0 * Real.log (Fintype.card V))) :=
        tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht using hlow t ht
    · filter_upwards [self_mem_nhdsWithin] with t ht using hupp t ht
  refine ⟨hT1, ?_, sub_nonneg.mpr (hle y), ?_⟩
  · have := hT1.sub_const (s y)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (t : ℝ) ≠ 0 := (Set.mem_Ioi.mp ht).ne'
    unfold ntpLoss
    rw [hinner, mul_add, mul_neg, mul_div_cancel₀ _ ht']
    ring
  · constructor
    · intro h0 v
      have := hle v
      linarith
    · intro hall
      have : M ≤ s y := ciSup_le hall
      linarith [hle y]


end PlatonicJEPA


open PlatonicJEPA Filter Topology in
theorem solution {V : Type*} [Fintype V] [Nonempty V] {k : ℕ}
    (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) :
    Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0)
      (𝓝 (⨆ v, ∑ i, h i * w v i)) ∧
    Tendsto (fun t : ℝ => t * ntpLoss w (fun i => h i / t) y) (𝓝[>] 0)
      (𝓝 ((⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i)) ∧
    0 ≤ (⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i ∧
    ((⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i = 0 ↔ ∀ v, ∑ i, h i * w v i ≤ ∑ i, h i * w y i) :=
  PlatonicJEPA.next_token_prediction_margin_limit w h y
