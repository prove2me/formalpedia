-- Prove2me | solution 1 for StochIneqPO.Monotone.exists_counterexample_of_not_regular17
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:38:29.97016+00:00
-- url     : https://prove2.me/submissions/6fdeb487-2792-45bc-8b99-c2a734969af2

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes



namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology

theorem cex_seq {E : Type*} [TopologicalSpace E] [PartialOrder E]
    (h17 : ¬ Regular17 E) :
    ∃ (w : ℕ → E) (z : E) (U : Set E), Monotone w ∧ U ∈ 𝓝 z ∧
      Tendsto (fun j => w (2 * j)) atTop (𝓝 z) ∧ ∀ j, w (2 * j + 1) ∉ U := by
  unfold Regular17 at h17
  push_neg at h17
  obtain ⟨x, y, z, hxy, hx, hy⟩ := h17
  obtain ⟨U, hU, hfreq⟩ := (Filter.not_tendsto_iff_exists_frequently_notMem).1 hy
  obtain ⟨b, hb, hbU⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hxm : Monotone x := monotone_nat_of_le_succ (fun n => (hxy n).1.trans (hxy n).2)
  refine ⟨fun m => if m % 2 = 0 then x (b (m / 2)) else y (b (m / 2)), z, U, ?_, hU, ?_, ?_⟩
  · apply monotone_nat_of_le_succ
    intro m
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have h1 : (2 * j) % 2 = 0 := by omega
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      have h3 : (2 * j) / 2 = j := by omega
      have h4 : (2 * j + 1) / 2 = j := by omega
      simp only [h1, h2, h3, h4]
      simpa using (hxy (b j)).1
    · have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * j + 1) / 2 = j := by omega
      have h4 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      simp only [h1, h2, h3, h4]
      simp
      exact (hxy (b j)).2.trans (hxm (Nat.succ_le_of_lt (hb (Nat.lt_succ_self j))))
  · have : (fun j => (fun m : ℕ => if m % 2 = 0 then x (b (m / 2)) else y (b (m / 2))) (2 * j))
        = fun j => x (b j) := by
      funext j
      have h1 : (2 * j) % 2 = 0 := by omega
      have h3 : (2 * j) / 2 = j := by omega
      simp [h1, h3]
    rw [this]
    exact hx.comp hb.tendsto_atTop
  · intro j
    have h1 : (2 * j + 1) % 2 = 1 := by omega
    have h3 : (2 * j + 1) / 2 = j := by omega
    simp [h1, h3, hbU j]

/-- Level sets (typewriter). -/
noncomputable def A (i : ℕ) : Set ℝ :=
  Set.Ico (((i : ℝ) - 2 ^ Nat.log 2 i) / 2 ^ Nat.log 2 i)
    (((i : ℝ) - 2 ^ Nat.log 2 i + 1) / 2 ^ Nat.log 2 i)

theorem measurableSet_A (i : ℕ) : MeasurableSet (A i) := measurableSet_Ico

theorem volume_A (i : ℕ) :
    (volume.restrict (Set.Ico (0:ℝ) 1)) (A i) ≤ ENNReal.ofReal (1 / 2 ^ Nat.log 2 i) := by
  calc (volume.restrict (Set.Ico (0:ℝ) 1)) (A i) ≤ volume (A i) := Measure.restrict_apply_le _ _
    _ = ENNReal.ofReal (1 / 2 ^ Nat.log 2 i) := by
      unfold A
      rw [Real.volume_Ico]
      congr 1
      field_simp
      ring

theorem tendsto_volume_A :
    Tendsto (fun i => (volume.restrict (Set.Ico (0:ℝ) 1)) (A i)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun i : ℕ => Nat.log 2 i) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨2 ^ N, fun i hi => ?_⟩
    exact Nat.le_log_of_pow_le (by norm_num) hi
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (2:ℝ) ^ n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (1 / (2:ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    simpa using ENNReal.tendsto_ofReal this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h2.comp h1)
    (fun i => zero_le) (fun i => volume_A i)

theorem mem_A_inf (ω : ℝ) (hω : ω ∈ Set.Ico (0:ℝ) 1) (M : ℕ) : ∃ i ≥ M, ω ∈ A i := by
  obtain ⟨h0, h1⟩ := hω
  set n := max M 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hMn : M ≤ n := le_max_left _ _
  set k := ⌊ω * 2 ^ n⌋₊ with hk
  have hpos : (0:ℝ) < 2 ^ n := by positivity
  have hk1 : k < 2 ^ n := by
    rw [hk, Nat.floor_lt (by positivity)]
    push_cast
    nlinarith
  have hlog : Nat.log 2 (2 ^ n + k) = n := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]; omega
  refine ⟨2 ^ n + k, ?_, ?_⟩
  · have := Nat.lt_two_pow_self (n := n)
    omega
  · unfold A
    rw [hlog]
    push_cast
    constructor
    · rw [div_le_iff₀ hpos]
      have := Nat.floor_le (a := ω * 2 ^ n) (by positivity)
      rw [← hk] at this
      linarith
    · rw [lt_div_iff₀ hpos]
      have := Nat.lt_floor_add_one (ω * 2 ^ n)
      rw [← hk] at this
      linarith

theorem notmem_A_inf (ω : ℝ) (M : ℕ) : ∃ i ≥ M, ω ∉ A i := by
  set n := max M 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hMn : M ≤ n := le_max_left _ _
  have hpos : (0:ℝ) < 2 ^ n := by positivity
  have hn2 : (2:ℝ) ≤ 2 ^ n := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
  have hlog1 : Nat.log 2 (2 ^ n) = n := Nat.log_pow (by norm_num) n
  have hlog2 : Nat.log 2 (2 ^ n + 1) = n := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · have : 2 ^ n ≥ 2 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      rw [pow_succ]; omega
  have hge : 2 ^ n ≥ M := by
    have := Nat.lt_two_pow_self (n := n)
    omega
  by_cases h : ω ∈ A (2 ^ n)
  · refine ⟨2 ^ n + 1, by omega, ?_⟩
    intro h'
    unfold A at h h'
    rw [hlog1] at h
    rw [hlog2] at h'
    push_cast at h h'
    have e1 : ((2:ℝ) ^ n - 2 ^ n + 1) / 2 ^ n = 1 / 2 ^ n := by ring
    have e2 : ((2:ℝ) ^ n + 1 - 2 ^ n) / 2 ^ n = 1 / 2 ^ n := by ring
    rw [e2] at h'
    rw [e1] at h
    linarith [h.2, h'.1]
  · exact ⟨2 ^ n, hge, h⟩


theorem exists_counterexample_core {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : ¬ Regular17 E) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ ω, Monotone fun i => X i ω) ∧
        (∃ z : E, TendstoInMeasure μ X atTop (fun _ => z)) ∧ ¬ ConvergesAS μ X := by
  obtain ⟨w, z, U, hw, hU, hwz, hwU⟩ := cex_seq h17
  classical
  refine ⟨ℝ, inferInstance, volume.restrict (Set.Ico (0:ℝ) 1), ⟨by simp⟩,
    fun i ω => if ω ∈ A i then w (2 * i + 1) else w (2 * i), ?_, ?_, ⟨z, ?_⟩, ?_⟩
  · intro i
    exact Measurable.ite (measurableSet_A i) measurable_const measurable_const
  · intro ω
    apply monotone_nat_of_le_succ
    intro i
    beta_reduce
    split_ifs <;> apply hw <;> omega
  · intro ε hε
    have hev : ∀ᶠ j in atTop, edist (w (2 * j)) z < ε := by
      have := hwz.eventually (EMetric.ball_mem_nhds z hε)
      filter_upwards [this] with j hj
      exact hj
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_volume_A
      (Eventually.of_forall fun i => zero_le) ?_
    filter_upwards [hev] with i hi
    apply measure_mono
    intro ω hω
    by_contra hnot
    simp only [Set.mem_setOf_eq] at hω
    rw [if_neg hnot] at hω
    exact absurd hi (not_lt.2 hω)
  · rintro ⟨Y, hY⟩
    have hY' := (ae_restrict_iff' measurableSet_Ico).1 hY
    have hbad : ∀ ω ∈ Set.Ico (0:ℝ) 1,
        ¬ Tendsto (fun i => (fun i ω => if ω ∈ A i then w (2 * i + 1) else w (2 * i)) i ω)
          atTop (𝓝 (Y ω)) := by
      intro ω hω hconv
      have hfr : ∃ᶠ j in atTop, ω ∉ A j := by
        rw [Filter.frequently_atTop]; exact fun M => by
          obtain ⟨i, hi, h⟩ := notmem_A_inf ω M; exact ⟨i, hi, h⟩
      have hfr2 : ∃ᶠ j in atTop, ω ∈ A j := by
        rw [Filter.frequently_atTop]; exact fun M => by
          obtain ⟨i, hi, h⟩ := mem_A_inf ω hω M; exact ⟨i, hi, h⟩
      haveI : NeBot (atTop ⊓ 𝓟 {j | ω ∉ A j}) := Filter.frequently_iff_neBot.1 hfr
      have h1 : Tendsto (fun i => if ω ∈ A i then w (2 * i + 1) else w (2 * i))
          (atTop ⊓ 𝓟 {j | ω ∉ A j}) (𝓝 (Y ω)) := hconv.mono_left inf_le_left
      have h2 : Tendsto (fun i => if ω ∈ A i then w (2 * i + 1) else w (2 * i))
          (atTop ⊓ 𝓟 {j | ω ∉ A j}) (𝓝 z) := by
        refine (hwz.mono_left inf_le_left).congr' ?_
        filter_upwards [mem_inf_of_right (mem_principal_self {j | ω ∉ A j})] with j hj
        exact (if_neg hj).symm
      have hYz : Y ω = z := tendsto_nhds_unique h1 h2
      rw [hYz] at hconv
      have hev := hconv.eventually_mem hU
      obtain ⟨j, hjU, hjA⟩ := (hev.and_frequently hfr2).exists
      beta_reduce at hjU
      rw [if_pos hjA] at hjU
      exact hwU j hjU
    have hall : ∀ᵐ ω ∂(volume : Measure ℝ), ω ∉ Set.Ico (0:ℝ) 1 := by
      filter_upwards [hY'] with ω hω hmem
      exact hbad ω hmem (hω hmem)
    have : volume (Set.Ico (0:ℝ) 1) = 0 := measure_eq_zero_iff_ae_notMem.2 hall
    simp at this

end StochIneqPO.Monotone

open StochIneqPO.Monotone
open MeasureTheory Filter

theorem solution {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : ¬ Regular17 E) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ ω, Monotone fun i => X i ω) ∧
        (∃ z : E, TendstoInMeasure μ X atTop (fun _ => z)) ∧ ¬ ConvergesAS μ X := by
  exact exists_counterexample_core h17
