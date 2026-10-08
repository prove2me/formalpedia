-- Prove2me | solution 1 for SmithRegenerative.Ergodic.count_div_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:26:38.976066+00:00
-- url     : https://prove2.me/submissions/5a6a0dcb-dc05-4bdf-9752-8ceef42ff024

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal

open MeasureTheory ProbabilityTheory Filter Topology


namespace SmithRegenerative.Ergodic

/-! ### Deterministic counting lemmas for an abstract epoch sequence -/

open Classical in
/-- The first index `k` with `s < T k`. -/
noncomputable def cnt (T : ℕ → ℝ) (hex : ∀ s, ∃ k, s < T k) (s : ℝ) : ℕ := Nat.find (hex s)

theorem cnt_spec (T : ℕ → ℝ) (hex : ∀ s, ∃ k, s < T k) (s : ℝ) : s < T (cnt T hex s) := by
  classical
  exact Nat.find_spec (hex s)

theorem cnt_min (T : ℕ → ℝ) (hex : ∀ s, ∃ k, s < T k) (s : ℝ) {k : ℕ} (hk : k < cnt T hex s) :
    T k ≤ s := by
  classical
  have := Nat.find_min (hex s) hk
  exact not_lt.1 this

theorem cnt_ncard (T : ℕ → ℝ) (hmono : Monotone T) (hex : ∀ s, ∃ k, s < T k) (s : ℝ) :
    {k : ℕ | T k ≤ s}.ncard = cnt T hex s := by
  have h : {k : ℕ | T k ≤ s} = (Finset.range (cnt T hex s) : Set ℕ) := by
    rw [Finset.coe_range]
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · intro hk
      by_contra h
      push_neg at h
      have := hmono h
      have := cnt_spec T hex s
      linarith
    · intro hk
      exact cnt_min T hex s hk
  rw [h, Set.ncard_coe_finset, Finset.card_range]

theorem cnt_pos (T : ℕ → ℝ) (hT0 : T 0 = 0) (hex : ∀ s, ∃ k, s < T k) {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ cnt T hex s := by
  by_contra h
  push_neg at h
  have h0 : cnt T hex s = 0 := by omega
  have := cnt_spec T hex s
  rw [h0, hT0] at this
  linarith

theorem cnt_tendsto (T : ℕ → ℝ) (hmono : Monotone T) (hex : ∀ s, ∃ k, s < T k) :
    Tendsto (cnt T hex) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro m
  refine ⟨T m, fun s hs => ?_⟩
  by_contra h
  push_neg at h
  have h1 := hmono h.le
  have h2 := cnt_spec T hex s
  linarith

theorem cnt_ge_of_le (T : ℕ → ℝ) (hmono : Monotone T) (hex : ∀ s, ∃ k, s < T k) {m : ℕ} {s : ℝ}
    (hs : T m ≤ s) : m < cnt T hex s := by
  by_contra h
  push_neg at h
  have h1 := hmono h
  have h2 := cnt_spec T hex s
  linarith

/-- Main deterministic limit: `s / cnt s → μ`. -/
theorem cnt_div_tendsto (T : ℕ → ℝ) (hmono : Monotone T) (hT0 : T 0 = 0)
    (hex : ∀ s, ∃ k, s < T k) {μ : ℝ} (hμ : 0 < μ)
    (hlim : Tendsto (fun k : ℕ => T k / k) atTop (𝓝 μ)) :
    Tendsto (fun s : ℝ => s / (cnt T hex s : ℝ)) atTop (𝓝 μ) := by
  have hc := cnt_tendsto T hmono hex
  have hd : Tendsto (fun s => cnt T hex s - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hc
  -- upper bound: T (cnt s) / cnt s → μ
  have hup : Tendsto (fun s : ℝ => T (cnt T hex s) / (cnt T hex s : ℝ)) atTop (𝓝 μ) :=
    hlim.comp hc
  -- lower bound: T (cnt s - 1) / cnt s → μ
  have hlow : Tendsto (fun s : ℝ => T (cnt T hex s - 1) / (cnt T hex s : ℝ)) atTop (𝓝 μ) := by
    have h1 : Tendsto (fun s : ℝ => T (cnt T hex s - 1) / ((cnt T hex s - 1 : ℕ) : ℝ)) atTop
        (𝓝 μ) := hlim.comp hd
    have h2 : Tendsto (fun s : ℝ => ((cnt T hex s - 1 : ℕ) : ℝ) / (((cnt T hex s - 1 : ℕ) : ℝ) + 1))
        atTop (𝓝 1) := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp hd
    have h3 := h1.mul h2
    rw [mul_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hpos := cnt_pos T hT0 hex hs
    have hcast : ((cnt T hex s : ℕ) : ℝ) = ((cnt T hex s - 1 : ℕ) : ℝ) + 1 := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
    rw [hcast]
    set d : ℕ := cnt T hex s - 1
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · rw [hd0]; simp [hT0]
    · have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hpos := cnt_pos T hT0 hex hs
    have hcpos : (0 : ℝ) < (cnt T hex s : ℝ) := by exact_mod_cast hpos
    apply div_le_div_of_nonneg_right _ hcpos.le
    exact cnt_min T hex s (by omega)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hpos := cnt_pos T hT0 hex hs
    have hcpos : (0 : ℝ) < (cnt T hex s : ℝ) := by exact_mod_cast hpos
    apply div_le_div_of_nonneg_right _ hcpos.le
    exact (cnt_spec T hex s).le

theorem cnt_inv_tendsto (T : ℕ → ℝ) (hmono : Monotone T) (hT0 : T 0 = 0)
    (hex : ∀ s, ∃ k, s < T k) {μ : ℝ} (hμ : 0 < μ)
    (hlim : Tendsto (fun k : ℕ => T k / k) atTop (𝓝 μ)) :
    Tendsto (fun s : ℝ => (cnt T hex s : ℝ) / s) atTop (𝓝 μ⁻¹) := by
  have := (cnt_div_tendsto T hmono hT0 hex hμ hlim).inv₀ hμ.ne'
  refine this.congr fun s => ?_
  rw [inv_div]

/-! ### Probabilistic input -/

theorem epoch_eq_sum {Ω : Type*} (t : ℕ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0) (k : ℕ) (ω : Ω) :
    SmithRegenerative.Equilibrium.epoch t k ω = ∑ i ∈ Finset.range k, t (i + 1) ω := by
  unfold SmithRegenerative.Equilibrium.epoch
  rw [Finset.sum_range_succ', ht0, add_zero]

theorem epoch_monotone {Ω : Type*} (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t (i + 1) ω) (ω : Ω) :
    Monotone (fun k => SmithRegenerative.Equilibrium.epoch t k ω) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [SmithRegenerative.Equilibrium.epoch]
  rw [Finset.sum_range_succ _ (k + 1)]
  have := hnn k ω
  linarith

theorem epoch_zero {Ω : Type*} (t : ℕ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0) (ω : Ω) :
    SmithRegenerative.Equilibrium.epoch t 0 ω = 0 := by
  simp [SmithRegenerative.Equilibrium.epoch, ht0]

theorem mean_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t) (hμ : Integrable (t 1) P) :
    0 < ∫ ω, t 1 ω ∂P := by
  rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (hren.nonneg 0)) hμ]
  have hA : MeasurableSet {ω | t 1 ω = 0} := (hren.measurable 0) (measurableSet_singleton 0)
  have hsupp : Function.support (t 1) = {ω | t 1 ω = 0}ᶜ := by
    ext ω; simp [Function.mem_support]
  rw [hsupp]
  by_contra h
  push_neg at h
  have h0 : P {ω | t 1 ω = 0}ᶜ = 0 := le_antisymm h bot_le
  have := measure_add_measure_compl (μ := P) hA
  rw [h0, add_zero, measure_univ] at this
  have := hren.not_ae_zero
  rw [‹P {ω | t 1 ω = 0} = 1›] at this
  exact lt_irrefl _ this

theorem epoch_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t) (ht0 : ∀ ω, t 0 ω = 0)
    (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => SmithRegenerative.Equilibrium.epoch t k ω / k) atTop
      (𝓝 (∫ ω, t 1 ω ∂P)) := by
  have h := strong_law_ae_real (fun i : ℕ => t (i + 1)) hμ
    (fun i j hij => hren.indep.indepFun hij) hren.identDistrib
  filter_upwards [h] with ω hω
  refine hω.congr fun k => ?_
  rw [epoch_eq_sum t ht0]

/-- The key almost-sure package: epochs are monotone, start at zero, grow to infinity,
and satisfy the strong law. -/
theorem epoch_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t) (ht0 : ∀ ω, t 0 ω = 0)
    (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, (∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch t k ω) ∧
      Tendsto (fun k : ℕ => SmithRegenerative.Equilibrium.epoch t k ω / k) atTop
        (𝓝 (∫ ω, t 1 ω ∂P)) := by
  filter_upwards [epoch_slln t hren ht0 hμ] with ω hω
  refine ⟨?_, hω⟩
  have hpos := mean_pos t hren hμ
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) * (SmithRegenerative.Equilibrium.epoch t k ω / k))
      atTop atTop :=
    Filter.Tendsto.atTop_mul_pos hpos tendsto_natCast_atTop_atTop hω
  have h2 : Tendsto (fun k : ℕ => SmithRegenerative.Equilibrium.epoch t k ω) atTop atTop := by
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    field_simp
  intro s
  obtain ⟨k, hk⟩ := (Filter.tendsto_atTop.1 h2 (s + 1)).exists
  exact ⟨k, by linarith⟩

theorem count_eq_cnt {Ω : Type*} (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t (i + 1) ω) (ω : Ω)
    (hex : ∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch t k ω) (s : ℝ) :
    count t s ω = cnt (fun k => SmithRegenerative.Equilibrium.epoch t k ω) hex s := by
  unfold count
  exact cnt_ncard _ (epoch_monotone t hnn ω) hex s

theorem count_div_tendsto_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => (count t s ω : ℝ) / s) atTop
      (𝓝 (∫ ω, t 1 ω ∂P)⁻¹) := by
  filter_upwards [epoch_ae t hren ht0 hμ] with ω hω
  obtain ⟨hex, hlim⟩ := hω
  have := cnt_inv_tendsto (fun k => SmithRegenerative.Equilibrium.epoch t k ω)
    (epoch_monotone t hren.nonneg ω) (epoch_zero t ht0 ω) hex (mean_pos t hren hμ) hlim
  refine this.congr fun s => ?_
  rw [count_eq_cnt t hren.nonneg ω hex s]

end SmithRegenerative.Ergodic

open SmithRegenerative.Ergodic


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => (count t s ω : ℝ) / s) atTop
      (𝓝 (∫ ω, t 1 ω ∂P)⁻¹) := by
  exact count_div_tendsto_core t hren ht0 hμ
