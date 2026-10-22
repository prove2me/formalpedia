-- Prove2me | solution 1 for UnifiedFBSDE.Cubic.eq_A_6_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:37:05.698036+00:00
-- url     : https://prove2.me/submissions/bfef39af-d99b-4b55-909f-cb64460c6af8

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

set_option autoImplicit false

theorem solution (ε y₁ h T : ℝ) (hε : 0 < ε) (hy₁ : y₁ < h) :
    let t₀ := T - 1 / (2 * ε * (h - y₁) ^ 2)
    let yt : ℝ → ℝ := fun t => y₁ + 1 / Real.sqrt (2 * ε * (t - T) + ((h - y₁) ^ 2)⁻¹)
    (∀ t, t₀ < t → t ≤ T →
      MeasureTheory.IntegrableOn (fun s => ε * (yt s - y₁) ^ 3) (Set.Icc t T) ∧
        yt t = h + ∫ s in t..T, ε * (yt s - y₁) ^ 3) ∧
    Filter.Tendsto yt (nhdsWithin t₀ (Set.Ioi t₀)) Filter.atTop ∧
    (1 / (2 * ε * (h - y₁) ^ 2) < T → 0 < t₀ ∧ t₀ < T) := by
  intro t₀ yt
  have hd : 0 < h - y₁ := sub_pos.2 hy₁
  set d := h - y₁ with hdd
  have hc : 0 < (d ^ 2)⁻¹ := inv_pos.2 (pow_pos hd 2)
  set u : ℝ → ℝ := fun s => 2 * ε * (s - T) + (d ^ 2)⁻¹ with hu
  have hq : 0 < 2 * ε * d ^ 2 := by positivity
  have ht0 : t₀ = T - 1 / (2 * ε * d ^ 2) := rfl
  have hut0 : u t₀ = 0 := by
    simp only [hu, ht0]
    field_simp
    ring
  have hupos : ∀ s, t₀ < s → 0 < u s := by
    intro s hs
    have : u s = 2 * ε * (s - t₀) := by
      have := hut0
      simp only [hu] at this ⊢
      linarith
    rw [this]
    have : 0 < s - t₀ := sub_pos.2 hs
    positivity
  have huT : u T = (d ^ 2)⁻¹ := by simp [hu]
  have hytdef : ∀ s, yt s = y₁ + 1 / Real.sqrt (u s) := fun s => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht htT
    have hpos : ∀ s ∈ Set.Icc t T, 0 < u s := by
      intro s hs
      exact hupos s (lt_of_lt_of_le ht hs.1)
    have hderiv : ∀ s ∈ Set.uIcc t T, HasDerivAt (fun s => -(Real.sqrt (u s))⁻¹)
        (ε * (yt s - y₁) ^ 3) s := by
      intro s hs
      rw [Set.uIcc_of_le htT] at hs
      have hp := hpos s hs
      have hu' : HasDerivAt u (2 * ε) s := by
        have := (((hasDerivAt_id s).sub_const T).const_mul (2 * ε)).add_const ((d ^ 2)⁻¹)
        simpa [hu] using this
      have hs1 := hu'.sqrt hp.ne'
      have hs2 : Real.sqrt (u s) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
      have hs3 : HasDerivAt (fun s => -(Real.sqrt (u s))⁻¹) _ s := (hs1.inv hs2).neg
      refine hs3.congr_deriv ?_
      have hyy : yt s - y₁ = 1 / Real.sqrt (u s) := by rw [hytdef]; ring
      rw [hyy]
      field_simp
    have hcont : ContinuousOn (fun s => ε * (yt s - y₁) ^ 3) (Set.Icc t T) := by
      have : ContinuousOn (fun s => ε * (1 / Real.sqrt (u s)) ^ 3) (Set.Icc t T) := by
        refine continuousOn_const.mul (ContinuousOn.pow (continuousOn_const.div ?_ ?_) 3)
        · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
        · intro s hs; exact (Real.sqrt_pos.2 (hpos s hs)).ne'
      refine this.congr (fun s _ => ?_)
      rw [hytdef]; ring_nf
    refine ⟨hcont.integrableOn_Icc, ?_⟩
    have hint : IntervalIntegrable (fun s => ε * (yt s - y₁) ^ 3) MeasureTheory.volume t T :=
      hcont.intervalIntegrable_of_Icc htT
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [huT]
    have h1 : Real.sqrt ((d ^ 2)⁻¹) = d⁻¹ := by
      rw [← inv_pow, Real.sqrt_sq (inv_nonneg.2 hd.le)]
    rw [h1, hytdef]
    simp only [inv_inv]
    have : h = y₁ + d := by simp [hdd]
    rw [this]
    simp only [one_div]
    ring
  · have h1 : Filter.Tendsto u (nhdsWithin t₀ (Set.Ioi t₀)) (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hcu : Continuous u := by simp only [hu]; fun_prop
        have := hcu.continuousAt.tendsto (x := t₀)
        rw [hut0] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs using hupos s hs
    have h2 : Filter.Tendsto Real.sqrt (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := Real.continuous_sqrt.continuousAt.tendsto (x := (0:ℝ))
        rw [Real.sqrt_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx using Real.sqrt_pos.2 hx
    have h3 := tendsto_inv_nhdsGT_zero.comp (h2.comp h1)
    have h4 := Filter.tendsto_atTop_add_const_left _ y₁ h3
    refine h4.congr (fun s => ?_)
    simp only [Function.comp, hytdef, one_div]
  · intro hT
    constructor
    · simp only [ht0]; linarith
    · simp only [ht0]; have : 0 < 1 / (2 * ε * d ^ 2) := by positivity
      linarith
