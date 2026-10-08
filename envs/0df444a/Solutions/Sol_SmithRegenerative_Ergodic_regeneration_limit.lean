-- Prove2me | solution 1 for SmithRegenerative.Ergodic.regeneration_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:29:54.874983+00:00
-- url     : https://prove2.me/submissions/6afa8a28-59c9-4f3f-9b53-7c87db4eb263

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

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

/-! ### Cumulative process material -/

theorem sum_Icc_one_eq (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

theorem count_tendsto_of_hex {Ω : Type*} (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t (i + 1) ω) (ω : Ω)
    (hex : ∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch t k ω) :
    Tendsto (fun s => count t s ω) atTop atTop := by
  have := cnt_tendsto (fun k => SmithRegenerative.Equilibrium.epoch t k ω)
    (epoch_monotone t hnn ω) hex
  refine this.congr fun s => ?_
  rw [count_eq_cnt t hnn ω hex s]

theorem incr_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hcum : IsCumulativeProcess P t w)
    (hκ : Integrable (cycleIncrement t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, cycleIncrement t w (i + 1) ω) / n) atTop
      (𝓝 (∫ ω, cycleIncrement t w 1 ω ∂P)) :=
  strong_law_ae_real (fun i : ℕ => cycleIncrement t w (i + 1)) hκ
    (fun i j hij => hcum.C1_indep.indepFun hij) hcum.C1_identDistrib

theorem eq_5_3_4_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) (hcum : IsCumulativeProcess P t w)
    (hκ : Integrable (cycleIncrement t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun s : ℝ => (∑ i ∈ Finset.Icc 1 (count t s ω + 1), cycleIncrement t w i ω) /
        ((count t s ω : ℝ) + 1))
      atTop (𝓝 (∫ ω, cycleIncrement t w 1 ω ∂P)) := by
  filter_upwards [epoch_ae t hren ht0 hμ, incr_slln t w hcum hκ] with ω hω hy
  obtain ⟨hex, _⟩ := hω
  have hc : Tendsto (fun s => count t s ω + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (count_tendsto_of_hex t hren.nonneg ω hex)
  have := hy.comp hc
  refine this.congr fun s => ?_
  simp only [Function.comp]
  rw [sum_Icc_one_eq]
  push_cast
  rfl

/-- Telescoping: `w (T_n) - w (T_0) = Σ_{i<n} y_{i+1}`. -/
theorem telescope {Ω : Type*} (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range n, cycleIncrement t w (i + 1) ω =
      w (SmithRegenerative.Equilibrium.epoch t n ω) ω -
        w (SmithRegenerative.Equilibrium.epoch t 0 ω) ω := by
  rw [← Finset.sum_range_sub (fun i => w (SmithRegenerative.Equilibrium.epoch t i ω) ω) n]
  apply Finset.sum_congr rfl
  intro i _
  simp [cycleIncrement]

theorem sZ_eq {Ω : Type*} (t : ℕ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0) (s : ℝ) (ω : Ω) :
    s + Z t s ω = SmithRegenerative.Equilibrium.epoch t (count t s ω + 1) ω := by
  unfold Z
  rw [epoch_eq_sum t ht0, sum_Icc_one_eq]
  ring

/-! ### Variation bounds -/

theorem variation_eq {Ω : Type*} (w : ℝ → Ω → ℝ) {ω : Ω} (hbv : HasBVPaths w ω) (s : ℝ) :
    variation w s ω = (eVariationOn (fun r => w r ω) (Set.Icc 0 s)).toReal := by
  unfold variation
  rw [if_pos hbv]

theorem abs_sub_le_variation {Ω : Type*} (w : ℝ → Ω → ℝ) {ω : Ω} (hbv : HasBVPaths w ω)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |w b ω - w a ω| ≤ variation w b ω - variation w a ω := by
  set f : ℝ → ℝ := fun r => w r ω with hf
  have hb : 0 ≤ b := ha.trans hab
  have hfin_b : eVariationOn f (Set.Icc 0 b) ≠ ⊤ := hbv b hb
  have hfin_a : eVariationOn f (Set.Icc 0 a) ≠ ⊤ := hbv a ha
  have hsum : eVariationOn f (Set.Icc 0 a) + eVariationOn f (Set.Icc a b) =
      eVariationOn f (Set.Icc 0 b) := by
    have := eVariationOn.Icc_add_Icc f (s := Set.univ) ha hab (Set.mem_univ a)
    simpa using this
  have hfin_ab : eVariationOn f (Set.Icc a b) ≠ ⊤ := by
    intro h
    rw [h, add_top] at hsum
    exact hfin_b hsum.symm
  have h1 : dist (f b) (f a) ≤ (eVariationOn f (Set.Icc a b)).toReal :=
    BoundedVariationOn.dist_le hfin_ab ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  rw [Real.dist_eq] at h1
  rw [variation_eq w hbv, variation_eq w hbv, ← hsum, ENNReal.toReal_add hfin_a hfin_ab]
  simp only [hf] at h1
  linarith

theorem variation_mono {Ω : Type*} (w : ℝ → Ω → ℝ) (ω : Ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    variation w a ω ≤ variation w b ω := by
  unfold variation
  split_ifs with hbv
  · apply ENNReal.toReal_mono (hbv b (ha.trans hab))
    exact eVariationOn.mono _ (Set.Icc_subset_Icc le_rfl hab)
  · exact le_rfl

theorem epoch_nonneg {Ω : Type*} (t : ℕ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0)
    (hnn : ∀ i ω, 0 ≤ t (i + 1) ω) (k : ℕ) (ω : Ω) :
    0 ≤ SmithRegenerative.Equilibrium.epoch t k ω := by
  rw [← epoch_zero t ht0 ω]
  exact epoch_monotone t hnn ω (Nat.zero_le k)

theorem abs_incr_le_var {Ω : Type*} (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0)
    (hnn : ∀ i ω, 0 ≤ t (i + 1) ω) {ω : Ω} (hbv : HasBVPaths w ω) (n : ℕ) :
    |cycleIncrement t w n ω| ≤ cycleVariation t w n ω := by
  unfold cycleIncrement cycleVariation
  exact abs_sub_le_variation w hbv (epoch_nonneg t ht0 hnn _ ω)
    (epoch_monotone t hnn ω (Nat.sub_le n 1))

theorem incr_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hcum : IsCumulativeProcess P t w)
    (hκ : Integrable (cycleVariation t w 1) P) : Integrable (cycleIncrement t w 1) P := by
  refine hκ.mono' (hcum.C1_identDistrib 0).aemeasurable_fst.aestronglyMeasurable ?_
  filter_upwards [hcum.C2] with ω hbv
  rw [Real.norm_eq_abs]
  exact abs_incr_le_var t w ht0 hren.nonneg hbv 1

theorem regeneration_limit_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w (s + Z t s ω) ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by
  have hy := incr_integrable t w hren ht0 hcum hκ
  filter_upwards [eq_5_3_4_core t w hren ht0 hμ hcum hy, count_div_tendsto_core t hren ht0 hμ]
    with ω h1 h2
  have h3 : Tendsto (fun s : ℝ => ((count t s ω : ℝ) + 1) / s) atTop (𝓝 (∫ ω, t 1 ω ∂P)⁻¹) := by
    have h4 := h2.add tendsto_inv_atTop_zero
    rw [add_zero] at h4
    refine h4.congr fun s => ?_
    rw [add_div, one_div]
  have h5 := h1.mul h3
  rw [div_eq_mul_inv]
  refine h5.congr fun s => ?_
  rw [sZ_eq t ht0, sum_Icc_one_eq, telescope, epoch_zero t ht0, hw0, sub_zero]
  have : ((count t s ω : ℝ) + 1) ≠ 0 := by positivity
  field_simp

end SmithRegenerative.Ergodic

open SmithRegenerative.Ergodic


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w (s + Z t s ω) ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by
  exact regeneration_limit_core t w hren ht0 hw0 hμ hcum hκ
