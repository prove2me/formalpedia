-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P44.multiband_high_loss
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:20:23.096213+00:00
-- url     : https://prove2.me/submissions/7defd156-c31d-49d7-92bd-70edeec9050e

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P44
open QAlgorithms.Papers.Independent.Advance50.P44
open Filter Topology

theorem solution {A : Type*} (l : Filter A) [NeBot l]
    (N : ℕ) (M : Fin (N + 1) → ℕ) (hM : ∀ i, 0 < M i)
    (eta : A → Fin (N + 1) → ℝ)
    (heta : ∀ᶠ t in l, ∀ i, 0 < eta t i ∧ eta t i < 1)
    (hlim : ∀ i, Tendsto (fun t => eta t i) l (nhds 0)) :
    Tendsto (fun t => multibandLossExpression N M (eta t) /
      (sInf (Set.range (fun i : Fin (N + 1) => (M i : ℝ) * eta t i)) /
        Real.log 2)) l (nhds 1) := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set f : ℝ → ℝ := fun x => -Real.log (1 - x) with hf
  have hd : HasDerivAt f 1 0 := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
    have h2 := (Real.hasDerivAt_log (show (1:ℝ) - 0 ≠ 0 by norm_num)).comp 0 h1
    have h3 := h2.neg
    have h3' : HasDerivAt f (-((1 - 0 : ℝ)⁻¹ * -1)) 0 := h3
    exact h3'.congr_deriv (by norm_num)
  have hs : Tendsto (slope f 0) (𝓝[≠] 0) (𝓝 1) := hasDerivAt_iff_tendsto_slope.mp hd
  have hr : ∀ i, Tendsto (fun t => -Real.log (1 - eta t i) / eta t i) l (𝓝 1) := by
    intro i
    have hg : Tendsto (fun t => eta t i) l (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hlim i, ?_⟩
      filter_upwards [heta] with t ht
      exact ne_of_gt (ht i).1
    refine (hs.comp hg).congr' ?_
    filter_upwards with t
    simp only [Function.comp, slope_def_field, hf, sub_zero, sub_self, Real.log_one, neg_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  have hev : ∀ᶠ t in l, ∀ i, dist (-Real.log (1 - eta t i) / eta t i) 1 < δ ∧
      (0 < eta t i ∧ eta t i < 1) :=
    eventually_all.mpr fun i =>
      ((Metric.tendsto_nhds.mp (hr i)) δ hδpos).and (heta.mono fun t ht => ht i)
  filter_upwards [hev] with t ht
  rw [Real.dist_eq]
  unfold multibandLossExpression
  set r : Fin (N + 1) → ℝ := fun i => -Real.log (1 - eta t i) / eta t i with hrdef
  have hr1 : ∀ i, 1 - δ < r i ∧ r i < 1 + δ := by
    intro i
    have := (ht i).1
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  have hx : ∀ i, 0 < (M i : ℝ) * eta t i := fun i =>
    mul_pos (by exact_mod_cast hM i) (ht i).2.1
  have hy : ∀ i, -(M i : ℝ) * Real.logb 2 (1 - eta t i) =
      ((M i : ℝ) * eta t i) * r i / Real.log 2 := by
    intro i
    have : eta t i ≠ 0 := (ht i).2.1.ne'
    simp only [hrdef, Real.logb]
    field_simp
  set X := Set.range (fun i : Fin (N + 1) => (M i : ℝ) * eta t i) with hX
  set Y := Set.range (fun i : Fin (N + 1) => -(M i : ℝ) * Real.logb 2 (1 - eta t i)) with hY
  have hXfin : X.Finite := Set.finite_range _
  have hYfin : Y.Finite := Set.finite_range _
  have hXne : X.Nonempty := Set.range_nonempty _
  have hYne : Y.Nonempty := Set.range_nonempty _
  obtain ⟨i0, hi0⟩ := hXne.csInf_mem hXfin
  have hmx : 0 < sInf X := by rw [← hi0]; exact hx i0
  have hxle : ∀ i, sInf X ≤ (M i : ℝ) * eta t i := fun i =>
    csInf_le hXfin.bddBelow ⟨i, rfl⟩
  have hlow : (1 - δ) * sInf X / Real.log 2 ≤ sInf Y := by
    apply le_csInf hYne
    rintro _ ⟨i, rfl⟩
    beta_reduce
    rw [hy i, div_le_div_iff_of_pos_right hc]
    calc (1 - δ) * sInf X ≤ (1 - δ) * ((M i : ℝ) * eta t i) :=
          mul_le_mul_of_nonneg_left (hxle i) (by linarith)
      _ ≤ ((M i : ℝ) * eta t i) * r i := by
          nlinarith [hx i, (hr1 i).1]
  have hup : sInf Y ≤ (1 + δ) * sInf X / Real.log 2 := by
    refine (csInf_le hYfin.bddBelow ⟨i0, rfl⟩).trans ?_
    beta_reduce
    rw [hy i0, div_le_div_iff_of_pos_right hc]
    have h0 : (M i0 : ℝ) * eta t i0 = sInf X := hi0
    rw [h0]
    nlinarith [(hr1 i0).2]
  have key : sInf Y / (sInf X / Real.log 2) = sInf Y * Real.log 2 / sInf X := by
    field_simp
  rw [key]
  have e1 : 1 - δ ≤ sInf Y * Real.log 2 / sInf X := by
    rw [le_div_iff₀ hmx]
    have := (div_le_iff₀ hc).mp hlow
    linarith
  have e2 : sInf Y * Real.log 2 / sInf X ≤ 1 + δ := by
    rw [div_le_iff₀ hmx]
    have := (le_div_iff₀ hc).mp hup
    linarith
  rw [abs_lt]
  constructor <;> linarith
