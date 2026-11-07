-- Prove2me | solution 1 for SmithRegenerative.CLT.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:51:43.746061+00:00
-- url     : https://prove2.me/submissions/b1ec38c0-8edd-485e-878b-756a8f076008

import Mathlib
import Theorems.Thm_SmithRegenerative_CLT_theorem_B_vector
import Theorems.Thm_SmithRegenerative_CLT_lemma_8
import Theorems.Thm_SmithRegenerative_CLT_renewal_slln

open MeasureTheory ProbabilityTheory Filter Topology


namespace SmithRegenerative.CLT.T10

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


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

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
  filter_upwards [SmithRegenerative.CLT.lemma_8 P τ w hw hμ 2 two_pos hκ] with ω hω
  refine hω.congr fun t => ?_
  rw [Real.sqrt_eq_rpow]

/-! ### Corollary 9·1 -/

theorem incr_sub_linear {Ω : Type*} (τ : ℕ → Ω → ℝ) (ht0 : ∀ ω, τ 0 ω = 0) (w : ℝ → Ω → ℝ)
    (c : ℝ) (n : ℕ) :
    incr (fun s ω => w s ω - c * s) τ n = fun ω => incr w τ n ω - c * τ n ω := by
  ext ω
  rcases n with _ | k
  · simp [incr, ht0]
  · simp only [incr, Nat.add_sub_cancel]
    have : SmithRegenerative.Equilibrium.epoch τ (k + 1) ω =
        SmithRegenerative.Equilibrium.epoch τ k ω + τ (k + 1) ω := by
      unfold SmithRegenerative.Equilibrium.epoch
      rw [Finset.sum_range_succ _ (k + 1)]
    rw [this]
    ring

theorem overshoot_div_sqrt_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (hτ : IsRenewal P τ) (hμ : Integrable (τ 1) P)
    (hμ2 : Integrable (fun ω => τ 1 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => overshoot τ t ω / Real.sqrt t) atTop (𝓝 0) := by
  have hmom : Integrable (fun ω => |τ 1 ω| ^ (2 : ℝ)) P := by
    refine hμ2.congr (Eventually.of_forall fun ω => ?_)
    simp only
    rw [Real.rpow_two, sq_abs]
  have hv := lemma_7_core τ 2 two_pos hτ.ident hmom
  have hbound : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      |overshoot τ t ω| ≤ τ (count τ t ω) ω + τ (count τ t ω + 1) ω := by
    filter_upwards [epoch_ae τ hτ hμ] with ω hω
    intro t ht
    exact overshoot_le τ hτ.delay_zero hτ.nonneg ω hω.1 ht
  filter_upwards [overshoot_tendsto_of_bound P τ hτ hμ (overshoot τ) τ 2 two_pos hv hbound]
    with ω hω
  refine hω.congr fun t => ?_
  rw [Real.sqrt_eq_rpow]

end SmithRegenerative.CLT.T10


open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT.T10

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem tendstoInMeasure_of_tendsto_ae_vec {M : ℕ} {f : ℝ → Ω → EuclideanSpace ℝ (Fin M)}
    {g : Ω → EuclideanSpace ℝ (Fin M)}
    (hf : ∀ t, AEStronglyMeasurable (f t) P)
    (hfg : ∀ᵐ ω ∂P, Tendsto (fun t => f t ω) atTop (𝓝 (g ω))) :
    TendstoInMeasure P f atTop g := by
  intro ε hε
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  exact tendstoInMeasure_of_tendsto_ae (fun n => hf (u n))
    (by filter_upwards [hfg] with ω h; exact h.comp hu) ε hε

/-- The single process `w i` is a cumulative process on the same renewal process. -/
theorem single_model {M : ℕ} (τ : ℕ → Ω → ℝ) (w : Fin M → ℝ → Ω → ℝ)
    (hw : IsCumulativeModel P τ w) (i : Fin M) :
    IsCumulativeModel P τ (fun _ : Fin 1 => w i) where
  renewal := hw.renewal
  measurable := fun _ s => hw.measurable i s
  start_zero := fun _ ω => hw.start_zero i ω
  boundedVariation := fun _ => hw.boundedVariation i
  indep := by
    have hg : Measurable (fun v : ℝ × (Fin M → ℝ) × (Fin M → ℝ) =>
        ((v.1, fun _ : Fin 1 => v.2.1 i, fun _ : Fin 1 => v.2.2 i) :
          ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ))) := by fun_prop
    exact hw.indep.comp _ (fun _ => hg)
  ident := by
    have hg : Measurable (fun v : ℝ × (Fin M → ℝ) × (Fin M → ℝ) =>
        ((v.1, fun _ : Fin 1 => v.2.1 i, fun _ : Fin 1 => v.2.2 i) :
          ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ))) := by fun_prop
    exact fun n => (hw.ident n).comp hg

theorem sum_Icc_one_eq' {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

/-- Telescoping: `Σ_{j=1}^{n_t+1} (y_j - κ) = w_{t+Z_t} - κ (n_t + 1)`. -/
theorem telescope (τ : ℕ → Ω → ℝ) (ht0 : ∀ ω, τ 0 ω = 0) (w : ℝ → Ω → ℝ)
    (hw0 : ∀ ω, w 0 ω = 0) (κ : ℝ) (t : ℝ) (ω : Ω) :
    ∑ j ∈ Finset.Icc 1 (count τ t ω + 1), (incr w τ j ω - κ) =
      w (t + overshoot τ t ω) ω - κ * ((count τ t ω : ℝ) + 1) := by
  rw [Finset.sum_sub_distrib, sum_Icc_one_eq']
  have e : ∑ i ∈ Finset.range (count τ t ω + 1), incr w τ (i + 1) ω =
      w (SmithRegenerative.Equilibrium.epoch τ (count τ t ω + 1) ω) ω -
        w (SmithRegenerative.Equilibrium.epoch τ 0 ω) ω := by
    rw [← Finset.sum_range_sub (fun i => w (SmithRegenerative.Equilibrium.epoch τ i ω) ω)]
    apply Finset.sum_congr rfl
    intro i _
    simp [incr]
  rw [e, epoch_zero τ ht0, hw0]
  have : t + overshoot τ t ω = SmithRegenerative.Equilibrium.epoch τ (count τ t ω + 1) ω := by
    unfold overshoot; ring
  rw [this]
  simp
  ring


theorem vec_core {M : ℕ} (τ : ℕ → Ω → ℝ) (hτ : IsRenewal P τ) (hμ : Integrable (τ 1) P)
    (w : Fin M → ℝ → Ω → ℝ) (hwm : ∀ i s, Measurable (w i s)) (hw0 : ∀ i ω, w i 0 ω = 0)
    (κ : Fin M → ℝ)
    (hy_indep : iIndepFun
      (fun j => fun ω => WithLp.toLp 2 (fun i => incr (w i) τ (j + 1) ω - κ i)) P)
    (hy_ident : ∀ j, IdentDistrib
      (fun ω => WithLp.toLp 2 (fun i => incr (w i) τ (j + 1) ω - κ i))
      (fun ω => WithLp.toLp 2 (fun i => incr (w i) τ 1 ω - κ i)) P P)
    (hy_L2 : ∀ l, MemLp (fun ω => incr (w l) τ 1 ω - κ l) 2 P)
    (hy_mean : ∀ l, ∫ ω, (incr (w l) τ 1 ω - κ l) ∂P = 0)
    (hover : ∀ i, ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ => (w i (t + overshoot τ t ω) ω - w i t ω) / Real.sqrt t) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
        (w i t ω - κ i * (count τ t ω : ℝ)) / Real.sqrt (t / mu1 P τ)))
      atTop id (fun _ => P)
      (multivariateGaussian 0 (covMatrix P (fun l ω => incr (w l) τ 1 ω - κ l))) := by
  set μ := mu1 P τ with hμdef
  have hμpos : 0 < μ := mean_pos τ hτ hμ
  set y : ℕ → Ω → EuclideanSpace ℝ (Fin M) :=
    fun j ω => WithLp.toLp 2 (fun i => incr (w i) τ j ω - κ i) with hy
  set ψ : ℝ → ℝ := fun t => t / μ with hψ
  have hψ_mono : Monotone ψ := fun a b hab => div_le_div_of_nonneg_right hab hμpos.le
  have hψ_unbdd : ¬ BddAbove (Set.range ψ) := by
    rintro ⟨C, hC⟩
    have h1 := hC ⟨(|C| + 1) * μ, rfl⟩
    simp only [hψ] at h1
    rw [mul_div_assoc, div_self hμpos.ne', mul_one] at h1
    have := le_abs_self C
    linarith
  set m : ℝ → Ω → ℕ := fun t ω => count τ t ω + 1 with hm
  have hm_meas : ∀ t, Measurable (m t) := fun t =>
    (count_measurable hτ.measurable hτ.nonneg t).add_const 1
  have hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1) := by
    refine tendstoInMeasure_of_tendsto_ae_real (fun t => ?_) ?_
    · exact ((measurable_from_nat.comp (hm_meas t)).div_const _).aestronglyMeasurable
    · filter_upwards [SmithRegenerative.CLT.renewal_slln P τ hτ hμ] with ω hω
      have h1 : Tendsto (fun t : ℝ => ((count τ t ω : ℝ) / t + 1 / t) * μ) atTop
          (𝓝 ((μ⁻¹ + 0) * μ)) :=
        (hω.add (tendsto_const_nhds.div_atTop tendsto_id)).mul tendsto_const_nhds
      rw [add_zero, inv_mul_cancel₀ hμpos.ne'] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [hm, hψ]
      push_cast
      field_simp
  have hA := SmithRegenerative.CLT.theorem_B_vector P ψ hψ_mono hψ_unbdd m hm_meas
    (fun _ _ => Nat.le_add_left 1 _) hm_ratio y hy_indep hy_ident
    (by simpa [hy] using hy_L2) (by simpa [hy] using hy_mean)
  have hcov : covMatrix P (fun l ω => y 1 ω l) =
      covMatrix P (fun l ω => incr (w l) τ 1 ω - κ l) := by
    simp [hy]
  rw [hcov] at hA
  set B : ℝ → Ω → EuclideanSpace ℝ (Fin M) := fun t ω => WithLp.toLp 2 (fun i =>
    (κ i - (w i (t + overshoot τ t ω) ω - w i t ω)) / Real.sqrt (t / μ)) with hB
  set F : ℝ → Ω → EuclideanSpace ℝ (Fin M) := fun t ω => WithLp.toLp 2 (fun i : Fin M =>
        (w i t ω - κ i * (count τ t ω : ℝ)) / Real.sqrt (t / μ)) with hF
  have key : ∀ t ω, F t ω =
      (Real.sqrt (ψ t))⁻¹ • ∑ j ∈ Finset.Icc 1 (m t ω), y j ω + B t ω := by
    intro t ω
    ext i
    simp only [hF, hB, hy, hm, hψ, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.toLp_apply, smul_eq_mul]
    rw [telescope τ hτ.delay_zero (w i) (hw0 i) (κ i) t ω]
    field_simp
    ring
  have hFm : ∀ t, Measurable (F t) := by
    intro t
    refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
    refine measurable_pi_lambda _ (fun i => ?_)
    exact ((hwm i t).sub ((measurable_from_nat.comp
      (count_measurable hτ.measurable hτ.nonneg t)).const_mul (κ i))).div_const _
  have hBae : ∀ t, AEStronglyMeasurable (B t) P := by
    intro t
    have e : B t = F t - (fun ω => (Real.sqrt (ψ t))⁻¹ • ∑ j ∈ Finset.Icc 1 (m t ω), y j ω) := by
      ext1 ω
      rw [Pi.sub_apply, key t ω]
      abel
    rw [e]
    exact (hFm t).aestronglyMeasurable.sub (hA.forall_aemeasurable t).aestronglyMeasurable
  have hBlim : TendstoInMeasure P B atTop (fun _ => (0 : EuclideanSpace ℝ (Fin M))) := by
    refine tendstoInMeasure_of_tendsto_ae_vec hBae ?_
    filter_upwards [ae_all_iff.2 hover] with ω hω
    have hcomp : ∀ i, Tendsto (fun t : ℝ =>
        (κ i - (w i (t + overshoot τ t ω) ω - w i t ω)) / Real.sqrt (t / μ)) atTop (𝓝 0) := by
      intro i
      have h1 : Tendsto (fun t : ℝ => κ i / Real.sqrt (t / μ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hμpos))
      have h2 : Tendsto (fun t : ℝ =>
          (w i (t + overshoot τ t ω) ω - w i t ω) / Real.sqrt t * Real.sqrt μ) atTop (𝓝 0) := by
        have := (hω i).mul_const (Real.sqrt μ)
        rwa [zero_mul] at this
      have h3 := h1.sub h2
      rw [sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμpos
      rw [Real.sqrt_div ht.le]
      field_simp
    have hpi : Tendsto (fun t : ℝ => fun i : Fin M =>
        (κ i - (w i (t + overshoot τ t ω) ω - w i t ω)) / Real.sqrt (t / μ)) atTop (𝓝 0) :=
      tendsto_pi_nhds.2 hcomp
    have h0 : (WithLp.toLp 2 (0 : Fin M → ℝ) : EuclideanSpace ℝ (Fin M)) = 0 := by simp
    have := ((PiLp.continuous_toLp 2 (fun _ : Fin M => ℝ)).tendsto 0).comp hpi
    rw [h0] at this
    exact this
  have hV := hA.add_of_tendstoInMeasure_const (Y := B) hBlim
    (fun t => (hBae t).aemeasurable)
  refine hV.congr (fun t => ?_) ?_
  · filter_upwards with ω
    simp only [Pi.add_apply]
    exact (key t ω).symm
  · filter_upwards with x
    simp

theorem theorem_10_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {M : ℕ} (τ : ℕ → Ω → ℝ) (w : Fin M → ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ w)
    (hμ : Integrable (τ 1) P)
    (hvar2 : ∀ i, Integrable (fun ω => varIncr (w i) τ 1 ω ^ 2) P) :
    TendstoInDistribution
      (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
        (w i t ω - (∫ ω', incr (w i) τ 1 ω' ∂P) * (count τ t ω : ℝ)) /
          Real.sqrt (t / mu1 P τ)))
      atTop id (fun _ => P)
      (multivariateGaussian 0 (covMatrix P (fun k => incr (w k) τ 1))) ∧
    (Integrable (fun ω => τ 1 ω ^ 2) P →
      TendstoInDistribution
        (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
          (w i t ω - (∫ ω', incr (w i) τ 1 ω' ∂P) / mu1 P τ * t) / Real.sqrt (t / mu1 P τ)))
        atTop id (fun _ => P)
        (multivariateGaussian 0 (covMatrix P (fun k ω =>
          incr (w k) τ 1 ω - (∫ ω', incr (w k) τ 1 ω' ∂P) / mu1 P τ * τ 1 ω)))) := by
  have hren := hw.renewal
  set κ : Fin M → ℝ := fun i => ∫ ω', incr (w i) τ 1 ω' ∂P with hκ
  set μ := mu1 P τ with hμdef
  have hμpos : 0 < μ := mean_pos τ hren hμ
  have hsingle := single_model τ w hw
  have hyL2 : ∀ l, MemLp (incr (w l) τ 1) 2 P := fun l =>
    incr_memLp_two τ (w l) (hsingle l) (hvar2 l)
  have hover : ∀ i, ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ => (w i (t + overshoot τ t ω) ω - w i t ω) / Real.sqrt t) atTop (𝓝 0) :=
    fun i => hover_of_lemma8 P τ (w i) (hsingle i) hμ (hvar2 i)
  constructor
  · have hg : Measurable (fun v : ℝ × (Fin M → ℝ) × (Fin M → ℝ) =>
        (WithLp.toLp 2 (fun i => v.2.1 i - κ i) : EuclideanSpace ℝ (Fin M))) :=
      (PiLp.continuous_toLp 2 _).measurable.comp (by fun_prop)
    have h := vec_core τ hren hμ w (fun i s => hw.measurable i s) (fun i ω => hw.start_zero i ω) κ
      (hw.indep.comp _ (fun _ => hg)) (fun j => (hw.ident j).comp hg)
      (fun l => (hyL2 l).sub (memLp_const _))
      (fun l => by
        rw [integral_sub ((hyL2 l).integrable one_le_two) (integrable_const _)]
        simp [hκ])
      hover
    have hcov : covMatrix P (fun l ω => incr (w l) τ 1 ω - κ l) =
        covMatrix P (fun k => incr (w k) τ 1) := by
      ext k l
      simp only [covMatrix]
      rw [covariance_sub_const_left ((hyL2 k).integrable one_le_two),
        covariance_sub_const_right ((hyL2 l).integrable one_le_two)]
    rw [hcov] at h
    exact h
  · intro hμ2
    set c : Fin M → ℝ := fun i => κ i / μ with hc
    set w' : Fin M → ℝ → Ω → ℝ := fun i s ω => w i s ω - c i * s with hw'
    have hincr : ∀ i n, incr (w' i) τ n = fun ω => incr (w i) τ n ω - c i * τ n ω :=
      fun i n => incr_sub_linear τ hren.delay_zero (w i) (c i) n
    have hτL2 : MemLp (τ 1) 2 P := by
      rw [memLp_two_iff_integrable_sq (hren.measurable 1).aestronglyMeasurable]
      exact hμ2
    have hg : Measurable (fun v : ℝ × (Fin M → ℝ) × (Fin M → ℝ) =>
        (WithLp.toLp 2 (fun i => v.2.1 i - c i * v.1 - 0) : EuclideanSpace ℝ (Fin M))) :=
      (PiLp.continuous_toLp 2 _).measurable.comp (by fun_prop)
    have hy_indep : iIndepFun
        (fun j => fun ω => (WithLp.toLp 2 (fun i => incr (w' i) τ (j + 1) ω - 0) :
          EuclideanSpace ℝ (Fin M))) P := by
      have := hw.indep.comp _ (fun _ => hg)
      convert this using 1
      ext j ω
      simp [hincr, cycleVec]
    have hy_ident : ∀ j, IdentDistrib
        (fun ω => (WithLp.toLp 2 (fun i => incr (w' i) τ (j + 1) ω - 0) :
          EuclideanSpace ℝ (Fin M)))
        (fun ω => (WithLp.toLp 2 (fun i => incr (w' i) τ 1 ω - 0) :
          EuclideanSpace ℝ (Fin M))) P P := by
      intro j
      have := (hw.ident j).comp hg
      convert this using 1 <;> (ext ω; simp [hincr, cycleVec])
    have hyL2' : ∀ l, MemLp (fun ω => incr (w' l) τ 1 ω - 0) 2 P := by
      intro l
      rw [hincr]
      exact ((hyL2 l).sub (hτL2.const_mul (c l))).sub (memLp_const _)
    have hmean' : ∀ l, ∫ ω, (incr (w' l) τ 1 ω - 0) ∂P = 0 := by
      intro l
      simp only [sub_zero]
      rw [hincr]
      rw [integral_sub ((hyL2 l).integrable one_le_two) ((hμ.const_mul (c l))),
        integral_const_mul]
      have e : ∫ a, τ 1 a ∂P = μ := rfl
      rw [e]
      simp only [hc, hκ]
      field_simp
      ring
    have hover' : ∀ i, ∀ᵐ ω ∂P,
        Tendsto (fun t : ℝ => (w' i (t + overshoot τ t ω) ω - w' i t ω) / Real.sqrt t) atTop
          (𝓝 0) := by
      intro i
      filter_upwards [hover i, overshoot_div_sqrt_tendsto P τ hren hμ hμ2] with ω h1 h2
      have h3 := h1.sub (h2.const_mul (c i))
      rw [mul_zero, sub_zero] at h3
      refine h3.congr fun t => ?_
      simp only [hw']
      ring
    have h := vec_core τ hren hμ w' (fun i s => (hw.measurable i s).sub measurable_const)
      (fun i ω => by simp [hw', hw.start_zero i ω]) (fun _ => 0) hy_indep hy_ident hyL2' hmean'
      hover'
    have e1 : (fun (t : ℝ) (ω : Ω) => (WithLp.toLp 2 (fun i : Fin M =>
          (w i t ω - κ i / μ * t) / Real.sqrt (t / μ)) : EuclideanSpace ℝ (Fin M))) =
        (fun (t : ℝ) (ω : Ω) => (WithLp.toLp 2 (fun i : Fin M =>
          (w' i t ω - (fun _ => (0 : ℝ)) i * (count τ t ω : ℝ)) / Real.sqrt (t / μ)) :
          EuclideanSpace ℝ (Fin M))) := by
      ext t ω i
      simp [hw', hc]
    have e2 : covMatrix P (fun k ω => incr (w k) τ 1 ω - κ k / μ * τ 1 ω) =
        covMatrix P (fun l ω => incr (w' l) τ 1 ω - (fun _ => (0 : ℝ)) l) := by
      simp only [hincr, sub_zero, hc]
    simp only [← hκ, ← hμdef]
    rw [e1, e2]
    exact h

end SmithRegenerative.CLT.T10

open SmithRegenerative.CLT

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {M : ℕ} (τ : ℕ → Ω → ℝ) (w : Fin M → ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ w)
    (hμ : Integrable (τ 1) P)
    (hvar2 : ∀ i, Integrable (fun ω => varIncr (w i) τ 1 ω ^ 2) P) :
    TendstoInDistribution
      (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
        (w i t ω - (∫ ω', incr (w i) τ 1 ω' ∂P) * (count τ t ω : ℝ)) /
          Real.sqrt (t / mu1 P τ)))
      atTop id (fun _ => P)
      (multivariateGaussian 0 (covMatrix P (fun k => incr (w k) τ 1))) ∧
    (Integrable (fun ω => τ 1 ω ^ 2) P →
      TendstoInDistribution
        (fun (t : ℝ) (ω : Ω) => WithLp.toLp 2 (fun i : Fin M =>
          (w i t ω - (∫ ω', incr (w i) τ 1 ω' ∂P) / mu1 P τ * t) / Real.sqrt (t / mu1 P τ)))
        atTop id (fun _ => P)
        (multivariateGaussian 0 (covMatrix P (fun k ω =>
          incr (w k) τ 1 ω - (∫ ω', incr (w k) τ 1 ω' ∂P) / mu1 P τ * τ 1 ω)))) :=
  SmithRegenerative.CLT.T10.theorem_10_core P τ w hw hμ hvar2
