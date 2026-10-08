-- Prove2me | solution 1 for SmithRegenerative.CLT.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:04:28.752477+00:00
-- url     : https://prove2.me/submissions/ecbe4975-623e-41a0-a803-7c2b37c3c15d

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology


namespace SmithRegenerative.CLT

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

/-- Main deterministic limit: `s / cnt s → μ`. -/
theorem cnt_div_tendsto (T : ℕ → ℝ) (hmono : Monotone T) (hT0 : T 0 = 0)
    (hex : ∀ s, ∃ k, s < T k) {μ : ℝ} (hμ : 0 < μ)
    (hlim : Tendsto (fun k : ℕ => T k / k) atTop (𝓝 μ)) :
    Tendsto (fun s : ℝ => s / (cnt T hex s : ℝ)) atTop (𝓝 μ) := by
  have hc := cnt_tendsto T hmono hex
  have hd : Tendsto (fun s => cnt T hex s - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hc
  have hup : Tendsto (fun s : ℝ => T (cnt T hex s) / (cnt T hex s : ℝ)) atTop (𝓝 μ) :=
    hlim.comp hc
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

theorem epoch_monotone {Ω : Type*} (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) (ω : Ω) :
    Monotone (fun k => SmithRegenerative.Equilibrium.epoch t k ω) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [SmithRegenerative.Equilibrium.epoch]
  rw [Finset.sum_range_succ _ (k + 1)]
  have := hnn (k + 1) ω
  linarith

theorem epoch_zero {Ω : Type*} (t : ℕ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0) (ω : Ω) :
    SmithRegenerative.Equilibrium.epoch t 0 ω = 0 := by
  simp [SmithRegenerative.Equilibrium.epoch, ht0]

theorem mean_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (hren : IsRenewal P t) (hμ : Integrable (t 1) P) :
    0 < mu1 P t := by
  unfold mu1
  rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (hren.nonneg 1)) hμ]
  have hA : MeasurableSet {ω | t 1 ω = 0} := (hren.measurable 1) (measurableSet_singleton 0)
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
    (t : ℕ → Ω → ℝ) (hren : IsRenewal P t) (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => SmithRegenerative.Equilibrium.epoch t k ω / k) atTop
      (𝓝 (mu1 P t)) := by
  have h := strong_law_ae_real (fun i : ℕ => t (i + 1)) hμ
    (fun i j hij => hren.indep.indepFun hij) hren.ident
  filter_upwards [h] with ω hω
  refine hω.congr fun k => ?_
  rw [epoch_eq_sum t hren.delay_zero]

/-- The key almost-sure package: epochs grow to infinity and satisfy the strong law. -/
theorem epoch_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (hren : IsRenewal P t) (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, (∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch t k ω) ∧
      Tendsto (fun k : ℕ => SmithRegenerative.Equilibrium.epoch t k ω / k) atTop
        (𝓝 (mu1 P t)) := by
  filter_upwards [epoch_slln t hren hμ] with ω hω
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

theorem count_eq_cnt {Ω : Type*} (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) (ω : Ω)
    (hex : ∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch t k ω) (s : ℝ) :
    count t s ω = cnt (fun k => SmithRegenerative.Equilibrium.epoch t k ω) hex s := by
  unfold count
  rw [show Nat.card { j : ℕ // SmithRegenerative.Equilibrium.epoch t j ω ≤ s } = {k : ℕ | SmithRegenerative.Equilibrium.epoch t k ω ≤ s}.ncard from rfl]
  exact cnt_ncard _ (epoch_monotone t hnn ω) hex s

theorem renewal_slln_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : IsRenewal P τ) (hμ : Integrable (τ 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (count τ t ω : ℝ) / t) atTop (𝓝 (mu1 P τ)⁻¹) := by
  filter_upwards [epoch_ae τ hτ hμ] with ω hω
  obtain ⟨hex, hlim⟩ := hω
  have := cnt_inv_tendsto (fun k => SmithRegenerative.Equilibrium.epoch τ k ω)
    (epoch_monotone τ hτ.nonneg ω) (epoch_zero τ hτ.delay_zero ω) hex (mean_pos τ hτ hμ) hlim
  refine this.congr fun s => ?_
  rw [count_eq_cnt τ hτ.nonneg ω hex s]

/-! ### Lemma 8 -/

theorem count_tendsto_of_hex {Ω : Type*} (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) (ω : Ω)
    (hex : ∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch t k ω) :
    Tendsto (fun s => count t s ω) atTop atTop := by
  have := cnt_tendsto (fun k => SmithRegenerative.Equilibrium.epoch t k ω)
    (epoch_monotone t hnn ω) hex
  refine this.congr fun s => ?_
  rw [count_eq_cnt t hnn ω hex s]

/-- The bounded-variation event of the definition of `variationProc`. -/
def HasBV {Ω : Type*} (w : ℝ → Ω → ℝ) (ω : Ω) : Prop :=
  ∀ s : ℝ, eVariationOn (fun u => w u ω) (Set.Icc 0 s) ≠ ⊤

theorem variationProc_eq {Ω : Type*} (w : ℝ → Ω → ℝ) {ω : Ω} (hbv : HasBV w ω) (s : ℝ) :
    variationProc w s ω = (eVariationOn (fun u => w u ω) (Set.Icc 0 s)).toReal := by
  unfold variationProc
  exact if_pos (hbv : ∀ s : ℝ, eVariationOn (fun u => w u ω) (Set.Icc 0 s) ≠ ⊤)

theorem abs_sub_le_variation {Ω : Type*} (w : ℝ → Ω → ℝ) {ω : Ω} (hbv : HasBV w ω)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |w b ω - w a ω| ≤ variationProc w b ω - variationProc w a ω := by
  set f : ℝ → ℝ := fun r => w r ω with hf
  have hfin_b : eVariationOn f (Set.Icc 0 b) ≠ ⊤ := hbv b
  have hfin_a : eVariationOn f (Set.Icc 0 a) ≠ ⊤ := hbv a
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
  rw [variationProc_eq w hbv, variationProc_eq w hbv, ← hsum, ENNReal.toReal_add hfin_a hfin_ab]
  simp only [hf] at h1
  linarith

theorem variationProc_mono {Ω : Type*} (w : ℝ → Ω → ℝ) (ω : Ω) {a b : ℝ} (hab : a ≤ b) :
    variationProc w a ω ≤ variationProc w b ω := by
  unfold variationProc
  split_ifs with hbv
  · apply ENNReal.toReal_mono (hbv b)
    exact eVariationOn.mono _ (Set.Icc_subset_Icc le_rfl hab)
  · exact le_rfl

theorem epoch_nonneg {Ω : Type*} (t : ℕ → Ω → ℝ) (ht0 : ∀ ω, t 0 ω = 0)
    (hnn : ∀ i ω, 0 ≤ t i ω) (k : ℕ) (ω : Ω) :
    0 ≤ SmithRegenerative.Equilibrium.epoch t k ω := by
  rw [← epoch_zero t ht0 ω]
  exact epoch_monotone t hnn ω (Nat.zero_le k)

theorem varIncr_nonneg {Ω : Type*} (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ)
    (hnn : ∀ i ω, 0 ≤ t i ω) (n : ℕ) (ω : Ω) : 0 ≤ varIncr w t n ω := by
  unfold varIncr
  have := variationProc_mono w ω (epoch_monotone t hnn ω (Nat.sub_le n 1))
  linarith

/-- Borel–Cantelli step: for a nonnegative integrable `X` and identically distributed
`Y n ~ X`, almost surely `Y n ≤ n` eventually. -/
theorem lemma_7_bc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : ℕ → Ω → ℝ) (hXint : Integrable X P) (hXnn : 0 ≤ X)
    (hid : ∀ n, IdentDistrib (Y (n + 1)) X P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Y n ω ≤ n := by
  have hsum : (∑' j : ℕ, P {ω | X ω ∈ Set.Ioi (j : ℝ)}) < ⊤ := by
    letI : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top (Ω := Ω) hXint hXnn
  set s : ℕ → Set Ω := fun n => {ω | Y (n + 1) ω ∈ Set.Ioi ((n : ℝ) + 1)} with hs
  have hmeas : ∀ n, P (s n) ≤ P {ω | X ω ∈ Set.Ioi (n : ℝ)} := by
    intro n
    have h1 : P (s n) = P {ω | X ω ∈ Set.Ioi ((n : ℝ) + 1)} :=
      (hid n).measure_mem_eq measurableSet_Ioi
    rw [h1]
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_Ioi] at hω ⊢
    linarith
  have hsum' : (∑' n, P (s n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hsum.ne (ENNReal.tsum_le_tsum hmeas)
  filter_upwards [ae_eventually_notMem hsum'] with ω hω
  rw [Filter.eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hN m (by omega)
  simp only [hs, Set.mem_setOf_eq, Set.mem_Ioi, not_lt] at this
  push_cast
  exact this

theorem lemma_7_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hident : ∀ n, IdentDistrib (x (n + 1)) (x 1) P P)
    (hmom : Integrable (fun ω => |x 1 ω| ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0) := by
  have key : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ((k : ℝ) + 1) * |x n ω| ^ p ≤ n := by
    intro k
    have hu : Measurable (fun y : ℝ => ((k : ℝ) + 1) * |y| ^ p) := by fun_prop
    refine lemma_7_bc (fun ω => ((k : ℝ) + 1) * |x 1 ω| ^ p)
      (fun n ω => ((k : ℝ) + 1) * |x n ω| ^ p) (hmom.const_mul _) (fun ω => by positivity)
      (fun n => ?_)
    exact (hident n).comp hu
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω
  have h1 : Tendsto (fun n : ℕ => |x n ω| ^ p / (n : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha (by positivity)
    · intro a ha
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt ha
      have h2 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
      filter_upwards [hω k, h2] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      calc |x n ω| ^ p / (n : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
            rw [div_le_div_iff₀ hnpos hkpos]
            linarith
        _ < a := hk
  have h2 : Tendsto (fun n : ℕ => (|x n ω| ^ p / (n : ℝ)) ^ (1 / p)) atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => y ^ (1 / p)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (1 / p))) :=
      (Real.continuous_rpow_const (by positivity)).tendsto 0
    rw [Real.zero_rpow (by positivity)] at hc
    exact hc.comp h1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine h2.congr fun n => ?_
  simp only [Function.comp]
  rw [Real.div_rpow (by positivity) (by positivity), one_div, Real.rpow_rpow_inv (abs_nonneg _) hp.ne',
    abs_div, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

theorem varIncr_identDistrib {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ)
    (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w)) (n : ℕ) :
    IdentDistrib (varIncr w τ (n + 1)) (varIncr w τ 1) P P := by
  have hm : Measurable (fun v : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) => v.2.2 0) := by fun_prop
  exact (hw.ident n).comp hm

theorem var_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (p : ℝ) (hp : 0 < p) (hκ : Integrable (fun ω => varIncr w τ 1 ω ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => varIncr w τ n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0) := by
  refine lemma_7_core (varIncr w τ) p hp (varIncr_identDistrib τ w hw) ?_
  refine hκ.congr (Eventually.of_forall fun ω => ?_)
  simp only
  rw [abs_of_nonneg (varIncr_nonneg τ w hw.renewal.nonneg 1 ω)]

theorem lemma_8_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P) (p : ℝ) (hp : 0 < p)
    (hκp : Integrable (fun ω => varIncr w τ 1 ω ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (w (t + overshoot τ t ω) ω - w t ω) / t ^ (1 / p))
      atTop (𝓝 0) := by
  have hren := hw.renewal
  have ht0 := hren.delay_zero
  have hbvae : ∀ᵐ ω ∂P, HasBV w ω := hw.boundedVariation 0
  filter_upwards [epoch_ae τ hren hμ, hbvae, var_slln τ w hw p hp hκp,
    renewal_slln_core P τ hren hμ] with ω hω hbv hvar hcnt
  obtain ⟨hex, _⟩ := hω
  set μ := mu1 P τ with hμdef
  have hμpos : 0 < μ := mean_pos τ hren hμ
  have hN : Tendsto (fun s => count τ s ω) atTop atTop := count_tendsto_of_hex τ hren.nonneg ω hex
  have hN1 : Tendsto (fun s => count τ s ω + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hc1 : Tendsto (fun s : ℝ => ((count τ s ω : ℝ) + 1) / s) atTop (𝓝 μ⁻¹) := by
    have h4 := hcnt.add tendsto_inv_atTop_zero
    rw [add_zero] at h4
    refine h4.congr fun s => ?_
    rw [add_div, one_div]
  have hrp : Continuous (fun y : ℝ => y ^ (1 / p)) := Real.continuous_rpow_const (by positivity)
  have hA : Tendsto (fun s : ℝ => varIncr w τ (count τ s ω) ω / (count τ s ω : ℝ) ^ (1 / p) *
      ((count τ s ω : ℝ) / s) ^ (1 / p)) atTop (𝓝 0) := by
    have h1 := hvar.comp hN
    have h2 := (hrp.tendsto μ⁻¹).comp hcnt
    have := h1.mul h2
    rw [zero_mul] at this
    exact this
  have hB : Tendsto (fun s : ℝ => varIncr w τ (count τ s ω + 1) ω /
      ((count τ s ω + 1 : ℕ) : ℝ) ^ (1 / p) * (((count τ s ω : ℝ) + 1) / s) ^ (1 / p)) atTop
      (𝓝 0) := by
    have h1 := hvar.comp hN1
    have h2 := (hrp.tendsto μ⁻¹).comp hc1
    have := h1.mul h2
    rw [zero_mul] at this
    exact this
  have hAB := hA.add hB
  rw [add_zero] at hAB
  refine squeeze_zero_norm' ?_ hAB
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  set N := count τ s ω with hNdef
  have hNpos : 1 ≤ N := by
    rw [hNdef, count_eq_cnt τ hren.nonneg ω hex s]
    exact cnt_pos _ (epoch_zero τ ht0 ω) hex hs.le
  have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hTN1 : SmithRegenerative.Equilibrium.epoch τ (N - 1) ω ≤ s := by
    rw [hNdef, count_eq_cnt τ hren.nonneg ω hex s]
    exact cnt_min _ hex s (by
      have := cnt_pos (fun k => SmithRegenerative.Equilibrium.epoch τ k ω) (epoch_zero τ ht0 ω) hex hs.le
      omega)
  have hTN : s < SmithRegenerative.Equilibrium.epoch τ N ω := by
    rw [hNdef, count_eq_cnt τ hren.nonneg ω hex s]
    exact cnt_spec _ hex s
  have hmono := epoch_monotone τ hren.nonneg ω
  have hTN2 : SmithRegenerative.Equilibrium.epoch τ N ω ≤
      SmithRegenerative.Equilibrium.epoch τ (N + 1) ω := hmono (Nat.le_succ N)
  have hover : s + overshoot τ s ω = SmithRegenerative.Equilibrium.epoch τ (N + 1) ω := by
    unfold overshoot; rw [← hNdef]; ring
  have hnum : |w (s + overshoot τ s ω) ω - w s ω| ≤
      varIncr w τ N ω + varIncr w τ (N + 1) ω := by
    rw [hover]
    have h1 := abs_sub_le_variation w hbv hs.le (hTN.le.trans hTN2)
    have h2 := variationProc_mono w ω hTN1
    unfold varIncr
    simp only [Nat.add_sub_cancel]
    linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
  have hsp : 0 < s ^ (1 / p) := Real.rpow_pos_of_pos hs _
  have hNp : 0 < (N : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos (by linarith) _
  have hN1p : 0 < ((N + 1 : ℕ) : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos (by positivity) _
  have e1 : ((N : ℝ) / s) ^ (1 / p) = (N : ℝ) ^ (1 / p) / s ^ (1 / p) :=
    Real.div_rpow (by positivity) hs.le _
  have e2 : (((N : ℝ) + 1) / s) ^ (1 / p) = ((N + 1 : ℕ) : ℝ) ^ (1 / p) / s ^ (1 / p) := by
    rw [Real.div_rpow (by positivity) hs.le]
    push_cast
    rfl
  rw [e1, e2]
  calc |w (s + overshoot τ s ω) ω - w s ω| / s ^ (1 / p)
      ≤ (varIncr w τ N ω + varIncr w τ (N + 1) ω) / s ^ (1 / p) :=
        div_le_div_of_nonneg_right hnum hsp.le
    _ = varIncr w τ N ω / (N : ℝ) ^ (1 / p) * ((N : ℝ) ^ (1 / p) / s ^ (1 / p)) +
        varIncr w τ (N + 1) ω / ((N + 1 : ℕ) : ℝ) ^ (1 / p) *
          (((N + 1 : ℕ) : ℝ) ^ (1 / p) / s ^ (1 / p)) := by
        field_simp


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Partial sums `S_k = Σ_{i<k} X_i`. -/
def psum (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, X i ω

theorem psum_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (k : ℕ) :
    Measurable (psum X k) := by
  unfold psum
  exact Finset.measurable_sum _ (fun i _ => hX i)

theorem psum_memLp {X : ℕ → Ω → ℝ} (hL2 : ∀ i, MemLp (X i) 2 P) (k : ℕ) :
    MemLp (psum X k) 2 P := by
  have := memLp_finsetSum' (Finset.range k) (fun i _ => hL2 i) (p := 2) (μ := P)
  convert this using 1
  ext ω; simp [psum]

theorem psum_sub {X : ℕ → Ω → ℝ} {k n : ℕ} (hkn : k ≤ n) (ω : Ω) :
    psum X n ω - psum X k ω = ∑ i ∈ Finset.Ico k n, X i ω := by
  unfold psum
  rw [← Finset.sum_range_add_sum_Ico _ hkn]
  ring

/-- Functions of disjoint blocks of an independent family are independent. -/
theorem indepFun_of_finset {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (S T : Finset ℕ) (hST : Disjoint S T) (G H : (ℕ → ℝ) → ℝ) (hG : Measurable G)
    (hH : Measurable H)
    (hGS : ∀ x y : ℕ → ℝ, (∀ i ∈ S, x i = y i) → G x = G y)
    (hHT : ∀ x y : ℕ → ℝ, (∀ i ∈ T, x i = y i) → H x = H y) :
    IndepFun (fun ω => G (fun i => X i ω)) (fun ω => H (fun i => X i ω)) P := by
  classical
  have h := hind.indepFun_finset S T hST hX
  let φ : (S → ℝ) → ℝ := fun v => G (fun i => if h : i ∈ S then v ⟨i, h⟩ else 0)
  let χ : (T → ℝ) → ℝ := fun v => H (fun i => if h : i ∈ T then v ⟨i, h⟩ else 0)
  have hφ : Measurable φ := by
    refine hG.comp (measurable_pi_lambda _ fun i => ?_)
    by_cases hi : i ∈ S
    · simp only [hi, dite_true]; exact measurable_pi_apply _
    · simp only [hi, dite_false]; exact measurable_const
  have hχ : Measurable χ := by
    refine hH.comp (measurable_pi_lambda _ fun i => ?_)
    by_cases hi : i ∈ T
    · simp only [hi, dite_true]; exact measurable_pi_apply _
    · simp only [hi, dite_false]; exact measurable_const
  have := h.comp hφ hχ
  convert this using 1
  · ext ω
    simp only [Function.comp, φ]
    apply hGS
    intro i hi
    simp [hi]
  · ext ω
    simp only [Function.comp, χ]
    apply hHT
    intro i hi
    simp [hi]

/-- The stopping sets `A k`: first `k` with `a ≤ |S_k|`. -/
def stopSet (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | a ≤ |psum X k ω| ∧ ∀ j < k, |psum X j ω| < a}

theorem stopSet_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (a : ℝ) (k : ℕ) :
    MeasurableSet (stopSet X a k) := by
  unfold stopSet
  simp only [Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (measurableSet_le measurable_const (psum_measurable hX k).abs) ?_
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (psum_measurable hX j).abs measurable_const

theorem stopSet_disjoint (X : ℕ → Ω → ℝ) (a : ℝ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (stopSet X a k) (stopSet X a l) := by
  rw [Set.disjoint_left]
  intro ω hk hl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact absurd hk.1 (not_le.2 (hl.2 k h))
  · exact absurd hl.1 (not_le.2 (hk.2 l h))

theorem subset_iUnion_stopSet (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) :
    {ω | ∃ k ≤ n, a ≤ |psum X k ω|} ⊆ ⋃ k ∈ Finset.range (n + 1), stopSet X a k := by
  classical
  intro ω hω
  obtain ⟨k, hkn, hk⟩ := hω
  have hex : ∃ k, a ≤ |psum X k ω| := ⟨k, hk⟩
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  refine ⟨Nat.find hex, by have := Nat.find_min' hex hk; omega, Nat.find_spec hex, ?_⟩
  intro j hj
  exact not_le.1 (Nat.find_min hex hj)

/-- **Kolmogorov's inequality.** -/
theorem kolmogorov_ineq {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    a ^ 2 * P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|} ≤ ∫ ω, psum X n ω ^ 2 ∂P := by
  classical
  have hSn : MemLp (psum X n) 2 P := psum_memLp hL2 n
  have hSn2 : Integrable (fun ω => psum X n ω ^ 2) P := hSn.integrable_sq
  -- key estimate on each stopping set
  have key : ∀ k ∈ Finset.range (n + 1),
      a ^ 2 * P.real (stopSet X a k) ≤ ∫ ω in stopSet X a k, psum X n ω ^ 2 ∂P := by
    intro k hk
    have hkn : k ≤ n := by simp at hk; omega
    set A := stopSet X a k with hA
    have hAm : MeasurableSet A := stopSet_measurable hX a k
    have hSk : MemLp (psum X k) 2 P := psum_memLp hL2 k
    set D : Ω → ℝ := fun ω => ∑ i ∈ Finset.Ico k n, X i ω with hD
    have hDL2 : MemLp D 2 P := by
      have := memLp_finsetSum' (Finset.Ico k n) (fun i _ => hL2 i) (p := 2) (μ := P)
      convert this using 1
      ext ω; simp [hD]
    have hDint : ∫ ω, D ω ∂P = 0 := by
      simp only [hD]
      rw [integral_finset_sum _ (fun i _ => (hL2 i).integrable one_le_two)]
      simp [h0]
    have hdecomp : ∀ ω, psum X n ω = psum X k ω + D ω := by
      intro ω
      have := psum_sub (X := X) hkn ω
      simp only [hD]; linarith
    -- the indicator-weighted S_k
    set F : Ω → ℝ := A.indicator (psum X k) with hF
    have hFL2 : MemLp F 2 P := hSk.indicator hAm
    -- independence of F and D
    have hFD : IndepFun F D P := by
      let G : (ℕ → ℝ) → ℝ := fun x =>
        if a ≤ |∑ i ∈ Finset.range k, x i| ∧ ∀ j < k, |∑ i ∈ Finset.range j, x i| < a
        then ∑ i ∈ Finset.range k, x i else 0
      let H : (ℕ → ℝ) → ℝ := fun x => ∑ i ∈ Finset.Ico k n, x i
      have hsum_meas : ∀ j, Measurable (fun x : ℕ → ℝ => ∑ i ∈ Finset.range j, x i) :=
        fun j => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have hG : Measurable G := by
        refine Measurable.ite ?_ (hsum_meas k) measurable_const
        simp only [Set.setOf_and, Set.setOf_forall]
        refine MeasurableSet.inter (measurableSet_le measurable_const (hsum_meas k).abs) ?_
        refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
        exact measurableSet_lt (hsum_meas j).abs measurable_const
      have hH : Measurable H := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have h := indepFun_of_finset hX hind (Finset.range k) (Finset.Ico k n)
        (by
          rw [Finset.disjoint_left]
          intro i hi hi'
          simp at hi hi'; omega) G H hG hH
        (by
          intro x y hxy
          have e : ∀ j ≤ k, ∑ i ∈ Finset.range j, x i = ∑ i ∈ Finset.range j, y i := by
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            apply hxy
            simp at hi ⊢; omega
          simp only [G]
          rw [e k le_rfl]
          congr 1
          apply propext
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun j hj => by rw [← e j hj.le]; exact h2 j hj⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun j hj => by rw [e j hj.le]; exact h2 j hj⟩)
        (by
          intro x y hxy
          simp only [H]
          exact Finset.sum_congr rfl (fun i hi => hxy i hi))
      convert h using 1
      ext ω
      simp only [hF, G, Set.indicator, hA, stopSet, Set.mem_setOf_eq, psum]
    have hFDint : ∫ ω, F ω * D ω ∂P = 0 := by
      rw [hFD.integral_fun_mul_eq_mul_integral hFL2.aestronglyMeasurable hDL2.aestronglyMeasurable,
        hDint, mul_zero]
    -- expand
    have hexp : ∫ ω in A, psum X n ω ^ 2 ∂P =
        (∫ ω in A, psum X k ω ^ 2 ∂P) + 2 * (∫ ω, F ω * D ω ∂P) + ∫ ω in A, D ω ^ 2 ∂P := by
      have e1 : ∫ ω in A, psum X n ω ^ 2 ∂P =
          ∫ ω in A, (psum X k ω ^ 2 + 2 * (psum X k ω * D ω) + D ω ^ 2) ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [hdecomp ω]; ring
      rw [e1]
      have i1 : IntegrableOn (fun ω => psum X k ω ^ 2) A P := hSk.integrable_sq.integrableOn
      have i2 : IntegrableOn (fun ω => psum X k ω * D ω) A P :=
        (hSk.integrable_mul hDL2).integrableOn
      have i3 : IntegrableOn (fun ω => D ω ^ 2) A P := hDL2.integrable_sq.integrableOn
      have i2' : IntegrableOn (fun ω => 2 * (psum X k ω * D ω)) A P := i2.const_mul 2
      have i12 : IntegrableOn (fun ω => psum X k ω ^ 2 + 2 * (psum X k ω * D ω)) A P :=
        i1.add i2'
      rw [integral_add i12 i3, integral_add i1 i2', integral_const_mul]
      have e2 : ∫ ω in A, psum X k ω * D ω ∂P = ∫ ω, F ω * D ω ∂P := by
        rw [← integral_indicator hAm]
        apply integral_congr_ae
        filter_upwards with ω
        simp only [hF, Set.indicator]
        split_ifs <;> simp
      rw [e2]
    have hD2 : 0 ≤ ∫ ω in A, D ω ^ 2 ∂P := integral_nonneg fun ω => by positivity
    have hSk2 : a ^ 2 * P.real A ≤ ∫ ω in A, psum X k ω ^ 2 ∂P := by
      refine setIntegral_ge_of_const_le_real hAm (measure_ne_top _ _) ?_
        hSk.integrable_sq.integrableOn
      intro ω hω
      have h1 : a ≤ |psum X k ω| := hω.1
      calc a ^ 2 ≤ |psum X k ω| ^ 2 := by gcongr
        _ = psum X k ω ^ 2 := sq_abs _
    rw [hexp, hFDint]
    linarith
  -- sum up
  have hsub := subset_iUnion_stopSet X a n
  have hmeasE : P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|} ≤
      ∑ k ∈ Finset.range (n + 1), P.real (stopSet X a k) := by
    calc P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|}
        ≤ P.real (⋃ k ∈ Finset.range (n + 1), stopSet X a k) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ k ∈ Finset.range (n + 1), P.real (stopSet X a k) :=
          measureReal_biUnion_finset_le _ _
  have hint : ∑ k ∈ Finset.range (n + 1), ∫ ω in stopSet X a k, psum X n ω ^ 2 ∂P ≤
      ∫ ω, psum X n ω ^ 2 ∂P := by
    rw [← integral_biUnion_finset _ (fun k _ => stopSet_measurable hX a k)
      (fun k _ l _ hkl => stopSet_disjoint X a hkl) (fun k _ => hSn2.integrableOn)]
    exact setIntegral_le_integral hSn2 (Eventually.of_forall fun ω => by positivity)
  calc a ^ 2 * P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|}
      ≤ a ^ 2 * ∑ k ∈ Finset.range (n + 1), P.real (stopSet X a k) := by gcongr
    _ = ∑ k ∈ Finset.range (n + 1), a ^ 2 * P.real (stopSet X a k) := Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), ∫ ω in stopSet X a k, psum X n ω ^ 2 ∂P :=
        Finset.sum_le_sum key
    _ ≤ _ := hint

theorem psum_shift (X : ℕ → Ω → ℝ) (b k : ℕ) (ω : Ω) :
    psum (fun j => X (b + j)) k ω = psum X (b + k) ω - psum X b ω := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    unfold psum at ih ⊢
    rw [Finset.sum_range_succ, ← add_assoc, Finset.sum_range_succ _ (b + k)]
    linarith

/-- Kolmogorov's inequality for a block of `d` summands starting at `b`, for an i.i.d. centred
sequence. -/
theorem kolmogorov_shift {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (h0 : ∫ ω, X 0 ω ∂P = 0) (b d : ℕ) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ k ≤ d, a ≤ |psum X (b + k) ω - psum X b ω|} ≤
      d * (∫ ω, X 0 ω ^ 2 ∂P) / a ^ 2 := by
  set X' : ℕ → Ω → ℝ := fun j => X (b + j) with hX'
  have hX'm : ∀ j, Measurable (X' j) := fun j => hX _
  have hind' : iIndepFun X' P := hind.precomp (g := fun j => b + j) (add_right_injective b)
  have hL2' : ∀ j, MemLp (X' j) 2 P := fun j => (hident _).memLp_iff.2 hL2
  have h0' : ∀ j, ∫ ω, X' j ω ∂P = 0 := fun j => by
    simp only [hX']; rw [(hident _).integral_eq, h0]
  have hk := kolmogorov_ineq hX'm hind' hL2' h0' d ha
  have hvar : ∫ ω, psum X' d ω ^ 2 ∂P = d * ∫ ω, X 0 ω ^ 2 ∂P := by
    have hm : Measurable (psum X' d) := psum_measurable hX'm d
    have hmean : ∫ ω, psum X' d ω ∂P = 0 := by
      unfold psum
      rw [integral_finsetSum _ (fun i _ => (hL2' i).integrable one_le_two)]
      simp [h0']
    rw [← variance_of_integral_eq_zero hm.aemeasurable hmean]
    have e : psum X' d = ∑ i ∈ Finset.range d, X' i := by ext ω; simp [psum]
    rw [e, IndepFun.variance_sum (fun i _ => hL2' i)
      (fun i _ j _ hij => hind'.indepFun hij)]
    have : ∀ i ∈ Finset.range d, variance (X' i) P = ∫ ω, X 0 ω ^ 2 ∂P := by
      intro i _
      rw [(hident _).variance_eq, variance_of_integral_eq_zero (hident 0).aemeasurable_fst h0]
    rw [Finset.sum_congr rfl this]
    simp
  rw [hvar] at hk
  have hset : {ω | ∃ k ≤ d, a ≤ |psum X (b + k) ω - psum X b ω|} =
      {ω | ∃ k ≤ d, a ≤ |psum X' k ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by rw [psum_shift]; exact h⟩
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by rw [psum_shift] at h; exact h⟩
  rw [hset, le_div_iff₀ (by positivity), mul_comm]
  exact hk

/-- A real number `r ∈ (0, 1]` below a positive `η : ℝ≥0∞`. -/
theorem exists_real_le_ennreal {η : ENNReal} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ η := by
  refine ⟨(min η 1).toReal, ?_, ?_⟩
  · apply ENNReal.toReal_pos
    · exact (lt_min hη zero_lt_one).ne'
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  · rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _

/-- **Anscombe's fluctuation estimate**: `(S_{m_t} − S_{⌊ψ t⌋})/(c √ψ(t)) → 0` in probability. -/
theorem anscombe_fluct {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (h0 : ∫ ω, X 0 ω ∂P = 0) (ψ : ℝ → ℝ) (hψ : Tendsto ψ atTop atTop)
    (m : ℝ → Ω → ℕ)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    {c : ℝ} (hc : 0 < c) :
    TendstoInMeasure P
      (fun t ω => (psum X (m t ω) ω - psum X ⌊ψ t⌋₊ ω) / (c * Real.sqrt (ψ t))) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨r, hr, hrη⟩ := exists_real_le_ennreal hη
  set v := ∫ ω, X 0 ω ^ 2 ∂P with hv
  have hv0 : 0 ≤ v := integral_nonneg fun ω => by positivity
  set δ : ℝ := r * ε ^ 2 * c ^ 2 / (20 * (v + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hbound : 10 * δ * v / (ε ^ 2 * c ^ 2) ≤ r / 2 := by
    rw [hδ]
    rw [div_le_iff₀ (by positivity)]
    have : 10 * (r * ε ^ 2 * c ^ 2 / (20 * (v + 1))) * v = r / 2 * (ε ^ 2 * c ^ 2) * (v / (v + 1)) := by
      field_simp
      ring
    rw [this]
    have h1 : v / (v + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h2 : 0 ≤ r / 2 * (ε ^ 2 * c ^ 2) := by positivity
    calc r / 2 * (ε ^ 2 * c ^ 2) * (v / (v + 1)) ≤ r / 2 * (ε ^ 2 * c ^ 2) * 1 := by gcongr
      _ = r / 2 * (ε ^ 2 * c ^ 2) := by ring
  -- the three eventual facts
  have hG : ∀ᶠ t in atTop, P {ω | δ ≤ ‖(m t ω : ℝ) / ψ t - 1‖} ≤ ENNReal.ofReal (r / 2) := by
    have := (tendstoInMeasure_iff_norm.1 hm_ratio) δ hδpos
    rw [ENNReal.tendsto_nhds_zero] at this
    exact this _ (by simp [hr])
  have hψ1 : ∀ᶠ t in atTop, 2 / δ ≤ ψ t ∧ 1 ≤ ψ t := by
    filter_upwards [hψ.eventually_ge_atTop (2 / δ), hψ.eventually_ge_atTop 1] with t h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hG, hψ1] with t hGt hψt
  obtain ⟨hψ2, hψ1'⟩ := hψt
  have hψpos : 0 < ψ t := by linarith
  set n : ℕ := ⌊ψ t⌋₊ with hn
  set d : ℕ := ⌈δ * ψ t⌉₊ + 1 with hd
  set a : ℝ := ε * (c * Real.sqrt (ψ t)) with ha
  have hsq : 0 < Real.sqrt (ψ t) := Real.sqrt_pos.2 hψpos
  have hapos : 0 < a := by positivity
  have ha2 : a ^ 2 = ε ^ 2 * c ^ 2 * ψ t := by
    rw [ha, mul_pow, mul_pow, Real.sq_sqrt hψpos.le]; ring
  have hnle : (n : ℝ) ≤ ψ t := Nat.floor_le hψpos.le
  have hnlt : ψ t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdlt : (d : ℝ) < δ * ψ t + 2 := by
    rw [hd]; push_cast
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ δ * ψ t)
    linarith
  have hdle : (d : ℝ) ≤ 2 * δ * ψ t := by
    have : 2 ≤ δ * ψ t := by
      rw [div_le_iff₀ hδpos] at hψ2; linarith
    linarith
  set b : ℕ := n - d with hb
  -- the three bad events
  set G' := {ω | δ ≤ ‖(m t ω : ℝ) / ψ t - 1‖} with hG'
  set U := {ω | ∃ k ≤ d, a ≤ |psum X (n + k) ω - psum X n ω|} with hU
  set L := {ω | ∃ k ≤ d, a / 2 ≤ |psum X (b + k) ω - psum X b ω|} with hL
  have hincl : {ω | ε ≤ ‖(psum X (m t ω) ω - psum X n ω) / (c * Real.sqrt (ψ t)) - 0‖} ⊆
      G' ∪ U ∪ L := by
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : 0 < c * Real.sqrt (ψ t)), le_div_iff₀ (by positivity : 0 < c * Real.sqrt (ψ t))] at hω
    -- hω : a ≤ |S m - S n|
    by_cases hGω : ω ∈ G'
    · exact Or.inl (Or.inl hGω)
    have hlt : |(m t ω : ℝ) / ψ t - 1| < δ := by
      simp only [hG', Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hGω; exact hGω
    have hmψ : |(m t ω : ℝ) - ψ t| < δ * ψ t := by
      have : (m t ω : ℝ) / ψ t - 1 = ((m t ω : ℝ) - ψ t) / ψ t := by field_simp
      rw [this, abs_div, abs_of_pos hψpos, div_lt_iff₀ hψpos] at hlt
      exact hlt
    rw [abs_lt] at hmψ
    have hceil : δ * ψ t ≤ (⌈δ * ψ t⌉₊ : ℝ) := Nat.le_ceil _
    have hm_le : m t ω ≤ n + d := by
      have : (m t ω : ℝ) < (n : ℝ) + d := by
        rw [hd]; push_cast; linarith
      exact_mod_cast this.le
    have hn_le : n ≤ m t ω + d := by
      have : (n : ℝ) < (m t ω : ℝ) + d := by
        rw [hd]; push_cast; linarith
      exact_mod_cast this.le
    rcases le_or_gt n (m t ω) with hnm | hnm
    · -- upper fluctuation
      refine Or.inl (Or.inr ⟨m t ω - n, by omega, ?_⟩)
      rw [Nat.add_sub_cancel' hnm]
      exact hω
    · -- lower fluctuation
      refine Or.inr ?_
      have hbm : b ≤ m t ω := by omega
      have hbn : b ≤ n := Nat.sub_le _ _
      by_contra hcon
      simp only [hL, Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
      have h1 := hcon (n - b) (by omega)
      have h2 := hcon (m t ω - b) (by omega)
      rw [Nat.add_sub_cancel' hbn] at h1
      rw [Nat.add_sub_cancel' hbm] at h2
      have : |psum X (m t ω) ω - psum X n ω| ≤
          |psum X (n + 0) ω - psum X b ω| + |psum X (m t ω) ω - psum X b ω| := by
        rw [add_zero]
        calc |psum X (m t ω) ω - psum X n ω|
            = |(psum X n ω - psum X b ω) - (psum X (m t ω) ω - psum X b ω)| := by
              rw [abs_sub_comm]; ring_nf
          _ ≤ _ := abs_sub _ _
      rw [add_zero] at this
      linarith
  have hU_bound : P U ≤ ENNReal.ofReal (d * v / a ^ 2) := by
    rw [← ofReal_measureReal (s := U)]
    exact ENNReal.ofReal_le_ofReal (kolmogorov_shift hX hind hident hL2 h0 n d hapos)
  have hL_bound : P L ≤ ENNReal.ofReal (d * v / (a / 2) ^ 2) := by
    rw [← ofReal_measureReal (s := L)]
    exact ENNReal.ofReal_le_ofReal (kolmogorov_shift hX hind hident hL2 h0 b d (by positivity))
  have hsum : d * v / a ^ 2 + d * v / (a / 2) ^ 2 ≤ r / 2 := by
    have e : d * v / a ^ 2 + d * v / (a / 2) ^ 2 = 5 * d * v / a ^ 2 := by
      field_simp
      ring
    rw [e, ha2]
    calc 5 * d * v / (ε ^ 2 * c ^ 2 * ψ t) ≤ 5 * (2 * δ * ψ t) * v / (ε ^ 2 * c ^ 2 * ψ t) := by
          gcongr
      _ = 10 * δ * v / (ε ^ 2 * c ^ 2) := by
          field_simp
          ring
      _ ≤ r / 2 := hbound
  calc P {ω | ε ≤ ‖(psum X (m t ω) ω - psum X n ω) / (c * Real.sqrt (ψ t)) - 0‖}
      ≤ P (G' ∪ U ∪ L) := measure_mono hincl
    _ ≤ P G' + P U + P L := by
        calc P (G' ∪ U ∪ L) ≤ P (G' ∪ U) + P L := measure_union_le _ _
          _ ≤ P G' + P U + P L := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (d * v / a ^ 2) +
        ENNReal.ofReal (d * v / (a / 2) ^ 2) := by gcongr
    _ = ENNReal.ofReal (r / 2) + ENNReal.ofReal (d * v / a ^ 2 + d * v / (a / 2) ^ 2) := by
        rw [add_assoc, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := by gcongr
    _ = ENNReal.ofReal r := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ η := hrη


/-! ### Assembling Theorem B -/

theorem tendstoInDistribution_comp {ι κ : Type*} {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ι → Ω → ℝ} {Z : Ω' → ℝ} {l : Filter ι}
    (h : TendstoInDistribution X l Z (fun _ => P) P') {l' : Filter κ} {g : κ → ι}
    (hg : Tendsto g l' l) :
    TendstoInDistribution (fun k => X (g k)) l' Z (fun _ => P) P' where
  forall_aemeasurable k := h.forall_aemeasurable (g k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hg

theorem tendstoInMeasure_const_of_tendsto {c : ℝ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) :
    TendstoInMeasure P (fun t (_ : Ω) => c t) atTop (fun _ => c₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h := (Metric.tendsto_nhds.1 hc) ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with t ht
  have : {x : Ω | ε ≤ ‖c t - c₀‖} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    rw [dist_eq_norm] at ht; exact ht
  rw [this, measure_empty]

theorem psum_random_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    {N : Ω → ℕ} (hN : Measurable N) : Measurable (fun ω => psum X (N ω) ω) := by
  have h : Measurable (fun p : Ω × ℕ => psum X p.2 p.1) :=
    measurable_from_prod_countable_left (fun k => psum_measurable hX k)
  exact h.comp (measurable_id.prodMk hN)

/-- Theorem B (in distribution) for a measurable i.i.d. sequence `X`, with `S_m = Σ_{i<m} X_i`. -/
theorem theorem_B_meas_dist {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (h0 : ∫ ω, X 0 ω ∂P = 0) (σ : ℝ) (hσ : 0 < σ) (hvar : variance (X 0) P = σ ^ 2)
    (ψ : ℝ → ℝ) (hψ : Tendsto ψ atTop atTop) (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t))
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1)) :
    TendstoInDistribution (fun t ω => psum X (m t ω) ω / (σ * Real.sqrt (ψ t))) atTop id
      (fun _ => P) (gaussianReal 0 1) := by
  -- normalised sequence
  set X' : ℕ → Ω → ℝ := fun k ω => X k ω / σ with hX'
  have hind' : iIndepFun X' P := hind.comp (fun _ x => x / σ) (fun _ => by fun_prop)
  have hident' : ∀ i, IdentDistrib (X' i) (X' 0) P P :=
    fun i => (hident i).comp (u := fun x => x / σ) (by fun_prop)
  have h0' : P[X' 0] = 0 := by
    simp only [hX']
    rw [integral_div, h0, zero_div]
  have h1' : P[X' 0 ^ 2] = 1 := by
    have : (X' 0 ^ 2) = fun ω => X 0 ω ^ 2 / σ ^ 2 := by
      ext ω; simp [hX', div_pow]
    rw [this, integral_div, ← variance_of_integral_eq_zero (hident 0).aemeasurable_fst h0, hvar,
      div_self (by positivity)]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (P := P) (P' := gaussianReal 0 1)
    (Y := id) HasLaw.id h0' h1' hind' hident'
  -- along `n t = ⌊ψ t⌋₊`
  have hn : Tendsto (fun t : ℝ => ⌊ψ t⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp hψ
  have hclt2 := tendstoInDistribution_comp hclt hn
  -- rescale by `√n/√ψ → 1`
  set c : ℝ → ℝ := fun t => Real.sqrt (⌊ψ t⌋₊ : ℝ) / Real.sqrt (ψ t) with hc
  have hc1 : Tendsto c atTop (𝓝 1) := by
    have h1 : Tendsto (fun t => (⌊ψ t⌋₊ : ℝ) / ψ t) atTop (𝓝 1) := by
      have hψpos : ∀ᶠ t in atTop, 0 < ψ t := hψ.eventually_gt_atTop 0
      have hlow : Tendsto (fun t => (ψ t - 1) / ψ t) atTop (𝓝 1) := by
        have : Tendsto (fun t => 1 - 1 / ψ t) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hψ)
        rw [sub_zero] at this
        refine this.congr' ?_
        filter_upwards [hψpos] with t ht
        field_simp
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [hψpos] with t ht
        apply div_le_div_of_nonneg_right _ ht.le
        have := Nat.lt_floor_add_one (ψ t); linarith
      · filter_upwards [hψpos] with t ht
        rw [div_le_one ht]; exact Nat.floor_le ht.le
    have h2 := (Real.continuous_sqrt.tendsto 1).comp h1
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards [hψ.eventually_gt_atTop 0] with t ht
    simp only [Function.comp, hc]
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
  have hslut := hclt2.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) (tendstoInMeasure_const_of_tendsto hc1)
    (fun _ => aemeasurable_const)
  -- target variable
  set V : ℝ → Ω → ℝ := fun t ω => psum X (m t ω) ω / (σ * Real.sqrt (ψ t)) with hV
  have hVm : ∀ t, Measurable (V t) := fun t =>
    (psum_random_measurable hX (hm_meas t)).div_const _
  have hfl := anscombe_fluct hX hind hident hL2 h0 ψ hψ m hm_ratio hσ
  dsimp only at hslut
  have hdiff : TendstoInMeasure P
      (V - fun t ω => ((Real.sqrt (⌊ψ t⌋₊ : ℝ))⁻¹ * ∑ k ∈ Finset.range ⌊ψ t⌋₊, X' k ω) * c t)
      atTop 0 := by
    refine hfl.congr' ?_ (by rfl)
    filter_upwards [hψ.eventually_ge_atTop 1] with t ht
    filter_upwards with ω
    have hψpos : 0 < ψ t := by linarith
    have hn1 : (1 : ℝ) ≤ (⌊ψ t⌋₊ : ℝ) := by
      have : 1 ≤ ⌊ψ t⌋₊ := Nat.le_floor (by simpa using ht)
      exact_mod_cast this
    have hsn : 0 < Real.sqrt (⌊ψ t⌋₊ : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hsψ : 0 < Real.sqrt (ψ t) := Real.sqrt_pos.2 hψpos
    simp only [Pi.sub_apply, hV, hc, hX', psum]
    rw [← Finset.sum_div]
    field_simp
  have hB : TendstoInDistribution V atTop id (fun _ => P) (gaussianReal 0 1) := by
    have h := tendstoInDistribution_of_tendstoInMeasure_sub V (fun ω : ℝ => id ω * 1) hslut
      hdiff (fun t => (hVm t).aemeasurable)
    have e : (fun ω : ℝ => id ω * 1) = id := by ext; simp
    rw [e] at h
    exact h
  exact hB

/-- Convergence in distribution to the standard normal law gives convergence of the distribution
functions at every point. -/
theorem cdf_of_tendstoInDistribution {V : ℝ → Ω → ℝ} (hVm : ∀ t, AEMeasurable (V t) P)
    (hB : TendstoInDistribution V atTop id (fun _ => P) (gaussianReal 0 1)) (α : ℝ) :
    Tendsto (fun t : ℝ => P.real {ω | V t ω ≤ α}) atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hB.tendsto
    (E := Set.Iic α) (by
      rw [frontier_Iic]
      change ((Measure.map id (gaussianReal 0 1)) {α}).toNNReal = 0
      rw [Measure.map_id]
      haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      rw [measure_singleton]
      rfl)
  have hlim' := (NNReal.continuous_coe.tendsto _).comp hlim
  convert hlim' using 2 with t
  · change P.real {ω | V t ω ≤ α} = (((P.map (V t)) (Set.Iic α)).toNNReal : ℝ)
    rw [ENNReal.coe_toNNReal_eq_toReal, Measure.map_apply_of_aemeasurable (hVm t) measurableSet_Iic,
      measureReal_def]
    rfl
  · change cdf (gaussianReal 0 1) α = (((Measure.map id (gaussianReal 0 1)) (Set.Iic α)).toNNReal : ℝ)
    rw [ENNReal.coe_toNNReal_eq_toReal, Measure.map_id, cdf_eq_real, measureReal_def]

theorem sum_Icc_one_eq (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

theorem theorem_B_dist_ae (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (hψ : Tendsto ψ atTop atTop)
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t))
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → ℝ) (hy_indep : iIndepFun (fun i => y (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P)
    (hy_L2 : MemLp (y 1) 2 P) (hy_mean : ∫ ω, y 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hy_var : variance (y 1) P = σ ^ 2) :
    TendstoInDistribution
      (fun (t : ℝ) ω => (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t))) atTop id
      (fun _ => P) (gaussianReal 0 1) := by
  have hyae : ∀ i, AEMeasurable (y (i + 1)) P := fun i => (hy_ident i).aemeasurable_fst
  set X : ℕ → Ω → ℝ := fun i => (hyae i).mk (y (i + 1)) with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => (hyae i).measurable_mk
  have hXeq : ∀ i, y (i + 1) =ᵐ[P] X i := fun i => (hyae i).ae_eq_mk
  have hind : iIndepFun X P := (iIndepFun_congr hXeq).1 hy_indep
  have hX0 : y 1 =ᵐ[P] X 0 := hXeq 0
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ((IdentDistrib.of_ae_eq (hyae i) (hXeq i)).symm.trans (hy_ident i)).trans
      (IdentDistrib.of_ae_eq (hyae 0) hX0)
  have hL2 : MemLp (X 0) 2 P := hy_L2.ae_eq hX0
  have h0 : ∫ ω, X 0 ω ∂P = 0 := by rw [← integral_congr_ae hX0]; exact hy_mean
  have hvar : variance (X 0) P = σ ^ 2 := by rw [← variance_congr hX0]; exact hy_var
  have hmain := theorem_B_meas_dist hXm hind hident hL2 h0 σ hσ_pos hvar ψ hψ m hm_meas hm_ratio
  refine hmain.congr (fun t => ?_) (by rfl)
  have hall : ∀ᵐ ω ∂P, ∀ i, y (i + 1) ω = X i ω := ae_all_iff.2 hXeq
  filter_upwards [hall] with ω hω
  rw [sum_Icc_one_eq]
  simp only [psum, hω]

theorem theorem_B_core (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (hψ_mono : Monotone ψ) (hψ_unbdd : ¬ BddAbove (Set.range ψ))
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t)) (hm_pos : ∀ t ω, 1 ≤ m t ω)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → ℝ) (hy_indep : iIndepFun (fun i => y (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P)
    (hy_L2 : MemLp (y 1) 2 P) (hy_mean : ∫ ω, y 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hy_var : variance (y 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  have hψ : Tendsto ψ atTop atTop := tendsto_atTop_atTop_of_monotone' hψ_mono hψ_unbdd
  have h := theorem_B_dist_ae P ψ hψ m hm_meas hm_ratio y hy_indep hy_ident hy_L2 hy_mean σ
    hσ_pos hy_var
  exact cdf_of_tendstoInDistribution h.forall_aemeasurable h


/-! ### Theorem 9 and Corollary 9·1 -/

theorem epoch_measurable {τ : ℕ → Ω → ℝ} (hτ : ∀ n, Measurable (τ n)) (k : ℕ) :
    Measurable (fun ω => SmithRegenerative.Equilibrium.epoch τ k ω) := by
  unfold SmithRegenerative.Equilibrium.epoch
  exact Finset.measurable_sum _ (fun i _ => hτ i)

open Classical in
theorem count_eq_find {τ : ℕ → Ω → ℝ} (hnn : ∀ i ω, 0 ≤ τ i ω) {t : ℝ} {ω : Ω}
    (hex : ∃ k, t < SmithRegenerative.Equilibrium.epoch τ k ω) :
    count τ t ω = Nat.find hex := by
  have hmono := epoch_monotone τ hnn ω
  unfold count
  rw [show Nat.card { j : ℕ // SmithRegenerative.Equilibrium.epoch τ j ω ≤ t } =
    {k : ℕ | SmithRegenerative.Equilibrium.epoch τ k ω ≤ t}.ncard from rfl]
  have h : {k : ℕ | SmithRegenerative.Equilibrium.epoch τ k ω ≤ t} =
      (Finset.range (Nat.find hex) : Set ℕ) := by
    rw [Finset.coe_range]
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · intro hk
      by_contra h
      push_neg at h
      have := hmono h
      have := Nat.find_spec hex
      linarith
    · intro hk
      exact not_lt.1 (Nat.find_min hex hk)
  rw [h, Set.ncard_coe_finset, Finset.card_range]

theorem count_eq_zero_of_forall {τ : ℕ → Ω → ℝ} {t : ℝ} {ω : Ω}
    (h : ∀ j, SmithRegenerative.Equilibrium.epoch τ j ω ≤ t) : count τ t ω = 0 := by
  unfold count
  have : Infinite { j : ℕ // SmithRegenerative.Equilibrium.epoch τ j ω ≤ t } := by
    refine Infinite.of_injective
      (fun j : ℕ => (⟨j, h j⟩ : { j : ℕ // SmithRegenerative.Equilibrium.epoch τ j ω ≤ t })) ?_
    intro a b hab
    exact congrArg Subtype.val hab
  exact Nat.card_eq_zero_of_infinite

theorem count_measurable {τ : ℕ → Ω → ℝ} (hτ : ∀ n, Measurable (τ n)) (hnn : ∀ i ω, 0 ≤ τ i ω)
    (t : ℝ) : Measurable (count τ t) := by
  classical
  refine measurable_to_countable' fun k => ?_
  rcases k with _ | k
  · have : count τ t ⁻¹' {0} = {ω | t < SmithRegenerative.Equilibrium.epoch τ 0 ω} ∪
        {ω | ∀ j, SmithRegenerative.Equilibrium.epoch τ j ω ≤ t} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq]
      by_cases hex : ∃ k, t < SmithRegenerative.Equilibrium.epoch τ k ω
      · rw [count_eq_find hnn hex]
        constructor
        · intro h
          left
          have := Nat.find_spec hex
          rw [h] at this
          exact this
        · rintro (h | h)
          · exact (Nat.find_eq_zero hex).2 h
          · obtain ⟨k, hk⟩ := hex
            exact absurd (h k) (not_le.2 hk)
      · push_neg at hex
        simp only [count_eq_zero_of_forall hex, true_iff]
        exact Or.inr hex
    rw [this]
    refine MeasurableSet.union (measurableSet_lt measurable_const (epoch_measurable hτ 0)) ?_
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (epoch_measurable hτ j) measurable_const
  · have : count τ t ⁻¹' {k + 1} = {ω | SmithRegenerative.Equilibrium.epoch τ k ω ≤ t} ∩
        {ω | t < SmithRegenerative.Equilibrium.epoch τ (k + 1) ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
      by_cases hex : ∃ k, t < SmithRegenerative.Equilibrium.epoch τ k ω
      · rw [count_eq_find hnn hex, Nat.find_eq_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨not_lt.1 (h2 k (by omega)), h1⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h2, fun n hn => not_lt.2 ?_⟩
          exact (epoch_monotone τ hnn ω (by omega : n ≤ k)).trans h1
      · push_neg at hex
        simp only [count_eq_zero_of_forall hex]
        constructor
        · intro h; omega
        · rintro ⟨_, h2⟩
          exact absurd (hex (k + 1)) (not_le.2 h2)
    rw [this]
    exact MeasurableSet.inter (measurableSet_le (epoch_measurable hτ k) measurable_const)
      (measurableSet_lt measurable_const (epoch_measurable hτ (k + 1)))

theorem tendstoInMeasure_of_tendsto_ae_real {f : ℝ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ t, AEStronglyMeasurable (f t) P)
    (hfg : ∀ᵐ ω ∂P, Tendsto (fun t => f t ω) atTop (𝓝 (g ω))) :
    TendstoInMeasure P f atTop g := by
  intro ε hε
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  exact tendstoInMeasure_of_tendsto_ae (fun n => hf (u n))
    (by filter_upwards [hfg] with ω h; exact h.comp hu) ε hε

/-- General overshoot estimate: if `|f t| ≤ v_{n_t} + v_{n_t+1}` and `v_n / n^{1/p} → 0`, then
`f t / t^{1/p} → 0` almost surely. -/
theorem overshoot_tendsto_of_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hren : IsRenewal P τ) (hμ : Integrable (τ 1) P)
    (f : ℝ → Ω → ℝ) (v : ℕ → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hv : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => v n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0))
    (hbound : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      |f t ω| ≤ v (count τ t ω) ω + v (count τ t ω + 1) ω) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => f t ω / t ^ (1 / p)) atTop (𝓝 0) := by
  have ht0 := hren.delay_zero
  filter_upwards [epoch_ae τ hren hμ, hv, hbound, renewal_slln_core P τ hren hμ]
    with ω hω hvar hb hcnt
  obtain ⟨hex, _⟩ := hω
  set μ := mu1 P τ with hμdef
  have hμpos : 0 < μ := mean_pos τ hren hμ
  have hN : Tendsto (fun s => count τ s ω) atTop atTop := count_tendsto_of_hex τ hren.nonneg ω hex
  have hN1 : Tendsto (fun s => count τ s ω + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hc1 : Tendsto (fun s : ℝ => ((count τ s ω : ℝ) + 1) / s) atTop (𝓝 μ⁻¹) := by
    have h4 := hcnt.add tendsto_inv_atTop_zero
    rw [add_zero] at h4
    refine h4.congr fun s => ?_
    rw [add_div, one_div]
  have hrp : Continuous (fun y : ℝ => y ^ (1 / p)) := Real.continuous_rpow_const (by positivity)
  have hA : Tendsto (fun s : ℝ => v (count τ s ω) ω / (count τ s ω : ℝ) ^ (1 / p) *
      ((count τ s ω : ℝ) / s) ^ (1 / p)) atTop (𝓝 0) := by
    have h1 := hvar.comp hN
    have h2 := (hrp.tendsto μ⁻¹).comp hcnt
    have := h1.mul h2
    rw [zero_mul] at this
    exact this
  have hB : Tendsto (fun s : ℝ => v (count τ s ω + 1) ω /
      ((count τ s ω + 1 : ℕ) : ℝ) ^ (1 / p) * (((count τ s ω : ℝ) + 1) / s) ^ (1 / p)) atTop
      (𝓝 0) := by
    have h1 := hvar.comp hN1
    have h2 := (hrp.tendsto μ⁻¹).comp hc1
    have := h1.mul h2
    rw [zero_mul] at this
    exact this
  have hAB := hA.add hB
  rw [add_zero] at hAB
  refine squeeze_zero_norm' ?_ hAB
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  set N := count τ s ω with hNdef
  have hNpos : 1 ≤ N := by
    rw [hNdef, count_eq_cnt τ hren.nonneg ω hex s]
    exact cnt_pos _ (epoch_zero τ ht0 ω) hex hs.le
  have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hnum := hb s hs
  rw [← hNdef] at hnum
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
  have hsp : 0 < s ^ (1 / p) := Real.rpow_pos_of_pos hs _
  have hNp : 0 < (N : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos (by linarith) _
  have hN1p : 0 < ((N + 1 : ℕ) : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos (by positivity) _
  have e1 : ((N : ℝ) / s) ^ (1 / p) = (N : ℝ) ^ (1 / p) / s ^ (1 / p) :=
    Real.div_rpow (by positivity) hs.le _
  have e2 : (((N : ℝ) + 1) / s) ^ (1 / p) = ((N + 1 : ℕ) : ℝ) ^ (1 / p) / s ^ (1 / p) := by
    rw [Real.div_rpow (by positivity) hs.le]
    push_cast
    rfl
  rw [e1, e2]
  calc |f s ω| / s ^ (1 / p)
      ≤ (v N ω + v (N + 1) ω) / s ^ (1 / p) :=
        div_le_div_of_nonneg_right hnum hsp.le
    _ = v N ω / (N : ℝ) ^ (1 / p) * ((N : ℝ) ^ (1 / p) / s ^ (1 / p)) +
        v (N + 1) ω / ((N + 1 : ℕ) : ℝ) ^ (1 / p) *
          (((N + 1 : ℕ) : ℝ) ^ (1 / p) / s ^ (1 / p)) := by
        field_simp

/-- The overshoot is at most `t_{n_t} + t_{n_t+1}`. -/
theorem overshoot_le (τ : ℕ → Ω → ℝ) (ht0 : ∀ ω, τ 0 ω = 0) (hnn : ∀ i ω, 0 ≤ τ i ω) (ω : Ω)
    (hex : ∀ s, ∃ k, s < SmithRegenerative.Equilibrium.epoch τ k ω) {t : ℝ} (ht : 0 < t) :
    |overshoot τ t ω| ≤ τ (count τ t ω) ω + τ (count τ t ω + 1) ω := by
  set N := count τ t ω with hNdef
  have hNpos : 1 ≤ N := by
    rw [hNdef, count_eq_cnt τ hnn ω hex t]
    exact cnt_pos _ (epoch_zero τ ht0 ω) hex ht.le
  have hTN1 : SmithRegenerative.Equilibrium.epoch τ (N - 1) ω ≤ t := by
    rw [hNdef, count_eq_cnt τ hnn ω hex t]
    exact cnt_min _ hex t (by
      have := cnt_pos (fun k => SmithRegenerative.Equilibrium.epoch τ k ω) (epoch_zero τ ht0 ω) hex ht.le
      omega)
  have hTN : t < SmithRegenerative.Equilibrium.epoch τ N ω := by
    rw [hNdef, count_eq_cnt τ hnn ω hex t]
    exact cnt_spec _ hex t
  have hmono := epoch_monotone τ hnn ω
  have hTN2 : SmithRegenerative.Equilibrium.epoch τ N ω ≤
      SmithRegenerative.Equilibrium.epoch τ (N + 1) ω := hmono (Nat.le_succ N)
  have hsum : SmithRegenerative.Equilibrium.epoch τ (N + 1) ω =
      SmithRegenerative.Equilibrium.epoch τ (N - 1) ω + τ N ω + τ (N + 1) ω := by
    unfold SmithRegenerative.Equilibrium.epoch
    rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ N]
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel]
  unfold overshoot
  rw [← hNdef, abs_of_nonneg (by linarith)]
  linarith

/-- The core of Theorem 9 / Corollary 9·1 with a general centering `κ₁ = E y₁`. -/
theorem clt_core (P : Measure Ω) [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (hτ : IsRenewal P τ)
    (hμ : Integrable (τ 1) P) (w : ℝ → Ω → ℝ) (hwm : ∀ s, Measurable (w s))
    (hw0 : ∀ ω, w 0 ω = 0)
    (hy_indep : iIndepFun (fun i => incr w τ (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (incr w τ (i + 1)) (incr w τ 1) P P)
    (hy_L2 : MemLp (incr w τ 1) 2 P)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ : variance (incr w τ 1) P = σ ^ 2)
    (hover : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (w (t + overshoot τ t ω) ω - w t ω) / Real.sqrt t)
      atTop (𝓝 0)) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (w t ω - (∫ ω', incr w τ 1 ω' ∂P) * (count τ t ω : ℝ)) /
          (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  set κ := ∫ ω', incr w τ 1 ω' ∂P with hκ
  set μ := mu1 P τ with hμdef
  have hμpos : 0 < μ := mean_pos τ hτ hμ
  -- centred increments
  set y : ℕ → Ω → ℝ := fun i ω => incr w τ i ω + (-κ) with hy
  have hy_indep' : iIndepFun (fun i => y (i + 1)) P :=
    hy_indep.comp (fun _ x => x + (-κ)) (fun _ => by fun_prop)
  have hy_ident' : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P := fun i =>
    (hy_ident i).comp (u := fun x => x + (-κ)) (by fun_prop)
  have hy_L2' : MemLp (y 1) 2 P := hy_L2.add (memLp_const _)
  have hy_mean' : ∫ ω, y 1 ω ∂P = 0 := by
    simp only [hy]
    rw [integral_add (hy_L2.integrable one_le_two) (integrable_const _)]
    simp [← hκ]
  have hy_var' : variance (y 1) P = σ ^ 2 := by
    simp only [hy]
    rw [variance_add_const hy_L2.aestronglyMeasurable, hσ]
  -- the time scale and the random index
  set ψ : ℝ → ℝ := fun t => t / μ with hψ
  have hψ_tend : Tendsto ψ atTop atTop := tendsto_id.atTop_div_const hμpos
  set m : ℝ → Ω → ℕ := fun t ω => count τ t ω + 1 with hm
  have hm_meas : ∀ t, Measurable (m t) := fun t =>
    (count_measurable hτ.measurable hτ.nonneg t).add_const 1
  have hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1) := by
    refine tendstoInMeasure_of_tendsto_ae_real (fun t => ?_) ?_
    · exact ((measurable_from_nat.comp (hm_meas t)).div_const _).aestronglyMeasurable
    · filter_upwards [renewal_slln_core P τ hτ hμ] with ω hω
      have h1 : Tendsto (fun t : ℝ => ((count τ t ω : ℝ) / t + 1 / t) * μ) atTop
          (𝓝 ((μ⁻¹ + 0) * μ)) :=
        (hω.add (tendsto_const_nhds.div_atTop tendsto_id)).mul tendsto_const_nhds
      rw [add_zero, inv_mul_cancel₀ hμpos.ne'] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [hm, hψ]
      push_cast
      field_simp
  have hA := theorem_B_dist_ae P ψ hψ_tend m hm_meas hm_ratio y hy_indep' hy_ident' hy_L2'
    hy_mean' σ hσ_pos hy_var'
  -- telescoping identity
  have htel : ∀ t ω, ∑ i ∈ Finset.Icc 1 (m t ω), y i ω =
      w (t + overshoot τ t ω) ω - κ * ((count τ t ω : ℝ) + 1) := by
    intro t ω
    simp only [hy, hm]
    rw [Finset.sum_add_distrib, sum_Icc_one_eq]
    have e : ∑ i ∈ Finset.range (count τ t ω + 1), incr w τ (i + 1) ω =
        w (SmithRegenerative.Equilibrium.epoch τ (count τ t ω + 1) ω) ω -
          w (SmithRegenerative.Equilibrium.epoch τ 0 ω) ω := by
      rw [← Finset.sum_range_sub (fun i => w (SmithRegenerative.Equilibrium.epoch τ i ω) ω)]
      apply Finset.sum_congr rfl
      intro i _
      simp [incr]
    rw [e, epoch_zero τ hτ.delay_zero, hw0]
    have : t + overshoot τ t ω = SmithRegenerative.Equilibrium.epoch τ (count τ t ω + 1) ω := by
      unfold overshoot; ring
    rw [this]
    simp
    ring
  -- the perturbation
  set B : ℝ → Ω → ℝ := fun t ω =>
    (κ - (w (t + overshoot τ t ω) ω - w t ω)) / (σ * Real.sqrt (t / μ)) with hB
  have hBae : ∀ t, AEStronglyMeasurable (B t) P := by
    intro t
    have e : B t = (fun ω => (w t ω - κ * (count τ t ω : ℝ)) / (σ * Real.sqrt (t / μ))) -
        (fun ω => (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t))) := by
      ext ω
      simp only [Pi.sub_apply, hB, hψ]
      rw [htel]
      ring
    rw [e]
    refine AEStronglyMeasurable.sub ?_ (hA.forall_aemeasurable t).aestronglyMeasurable
    refine Measurable.aestronglyMeasurable ?_
    exact ((hwm t).sub ((measurable_from_nat.comp
      (count_measurable hτ.measurable hτ.nonneg t)).const_mul κ)).div_const _
  have hBlim : TendstoInMeasure P B atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae_real hBae ?_
    filter_upwards [hover] with ω hω
    have h1 : Tendsto (fun t : ℝ => κ / (σ * Real.sqrt (t / μ))) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      apply Tendsto.const_mul_atTop hσ_pos
      exact Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hμpos)
    have h2 : Tendsto (fun t : ℝ =>
        (w (t + overshoot τ t ω) ω - w t ω) / Real.sqrt t * (Real.sqrt μ / σ)) atTop (𝓝 0) := by
      have := hω.mul_const (Real.sqrt μ / σ)
      rwa [zero_mul] at this
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [hB, Pi.zero_apply]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμpos
    rw [Real.sqrt_div ht.le]
    field_simp
  have hV := hA.add_of_tendstoInMeasure_const (Y := B) hBlim
    (fun t => (hBae t).aemeasurable)
  have hV' : TendstoInDistribution
      (fun t ω => (w t ω - κ * (count τ t ω : ℝ)) / (σ * Real.sqrt (t / μ))) atTop id
      (fun _ => P) (gaussianReal 0 1) := by
    refine hV.congr (fun t => ?_) ?_
    · filter_upwards with ω
      simp only [Pi.add_apply, hB, hψ]
      rw [htel, ← add_div]
      ring_nf
    · filter_upwards with x
      simp
  intro α
  exact cdf_of_tendstoInDistribution hV'.forall_aemeasurable hV' α

theorem incr_identDistrib {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ)
    (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w)) (n : ℕ) :
    IdentDistrib (incr w τ (n + 1)) (incr w τ 1) P P := by
  have hm : Measurable (fun v : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) => v.2.1 0) := by fun_prop
  exact (hw.ident n).comp hm

theorem incr_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ)
    (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w)) :
    iIndepFun (fun n => incr w τ (n + 1)) P := by
  have hm : Measurable (fun v : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) => v.2.1 0) := by fun_prop
  exact hw.indep.comp (fun _ => fun v : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) => v.2.1 0) (fun _ => hm)

theorem abs_incr_le_varIncr {Ω : Type*} (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (ht0 : ∀ ω, τ 0 ω = 0)
    (hnn : ∀ i ω, 0 ≤ τ i ω) {ω : Ω} (hbv : HasBV w ω) (n : ℕ) :
    |incr w τ n ω| ≤ varIncr w τ n ω := by
  unfold incr varIncr
  exact abs_sub_le_variation w hbv (epoch_nonneg τ ht0 hnn _ ω)
    (epoch_monotone τ hnn ω (Nat.sub_le n 1))

theorem incr_memLp_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ)
    (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P) : MemLp (incr w τ 1) 2 P := by
  have hae : AEStronglyMeasurable (incr w τ 1) P :=
    (incr_identDistrib τ w hw 0).aemeasurable_fst.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hae]
  refine hvar2.mono' (hae.pow 2) ?_
  filter_upwards [hw.boundedVariation 0] with ω hbv
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have := abs_incr_le_varIncr τ w hw.renewal.delay_zero hw.renewal.nonneg hbv 1
  gcongr

theorem hover_of_lemma8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P) (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (w (t + overshoot τ t ω) ω - w t ω) / Real.sqrt t)
      atTop (𝓝 0) := by
  have hκ : Integrable (fun ω => varIncr w τ 1 ω ^ (2 : ℝ)) P := by
    simpa [Real.rpow_two] using hvar2
  filter_upwards [lemma_8_core P τ w hw hμ 2 two_pos hκ] with ω hω
  refine hω.congr fun t => ?_
  rw [Real.sqrt_eq_rpow]

theorem theorem_9_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P)
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P)
    (hmean : ∫ ω, incr w τ 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ : variance (incr w τ 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | w t ω / (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  have h := clt_core P τ hw.renewal hμ w (hw.measurable 0) (hw.start_zero 0) (incr_indep τ w hw)
    (incr_identDistrib τ w hw) (incr_memLp_two τ w hw hvar2) σ hσ_pos hσ
    (hover_of_lemma8 P τ w hw hμ hvar2)
  simpa only [hmean, zero_mul, sub_zero] using h


end SmithRegenerative.CLT

open SmithRegenerative.CLT


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P)
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P)
    (hmean : ∫ ω, incr w τ 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ : variance (incr w τ 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | w t ω / (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  exact theorem_9_core P τ w hw hμ hvar2 hmean σ hσ_pos hσ
