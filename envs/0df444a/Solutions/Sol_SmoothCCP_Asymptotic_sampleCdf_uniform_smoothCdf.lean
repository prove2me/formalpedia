-- Prove2me | solution 1 for SmoothCCP.Asymptotic.sampleCdf_uniform_smoothCdf
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:45:28.439562+00:00
-- url     : https://prove2.me/submissions/80f6358c-ecbb-4547-bc7c-29cd70390bf6

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Theorems.Thm_GlivenkoCantelli_glivenko_cantelli

open MeasureTheory Filter Topology
open SmoothCCP.Feasibility
open scoped ENNReal

namespace SolSampleAux

/-! ### Empirical measure -/

noncomputable def empM {Ξ : Type} [MeasurableSpace Ξ] (N : ℕ) (s : ℕ → Ξ) : Measure Ξ :=
  ((N : ℝ≥0∞)⁻¹) • ∑ i ∈ Finset.range N, Measure.dirac (s i)

theorem empM_univ {Ξ : Type} [MeasurableSpace Ξ] {N : ℕ} (hN : 1 ≤ N) (s : ℕ → Ξ) :
    empM N s Set.univ = 1 := by
  unfold empM
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  have h0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top N)

theorem empM_prob {Ξ : Type} [MeasurableSpace Ξ] {N : ℕ} (hN : 1 ≤ N) (s : ℕ → Ξ) :
    IsProbabilityMeasure (empM N s) := ⟨empM_univ hN s⟩

theorem integral_empM {Ξ : Type} [MeasurableSpace Ξ] (N : ℕ) (s : ℕ → Ξ) {h : Ξ → ℝ}
    (hh : Measurable h) :
    ∫ y, h y ∂(empM N s) = (1 / (N : ℝ)) * ∑ i ∈ Finset.range N, h (s i) := by
  unfold empM
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp only [integral_dirac' h _ hh.stronglyMeasurable, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, smul_eq_mul, one_div]
  · intro i _
    exact integrable_dirac' hh.stronglyMeasurable (by simp)

theorem empM_real {Ξ : Type} [MeasurableSpace Ξ] (N : ℕ) (s : ℕ → Ξ) {A : Set Ξ}
    (hA : MeasurableSet A) :
    (empM N s).real A = (1 / (N : ℝ)) * ∑ i ∈ Finset.range N, A.indicator (fun _ => (1 : ℝ)) (s i) := by
  rw [← integral_indicator_one hA, integral_empM N s (measurable_one.indicator hA)]
  rfl

/-! ### Layer-cake discretisation -/

noncomputable def lay (k : ℕ) (v : ℝ) : ℝ :=
  (1 / (k : ℝ)) * ∑ j ∈ Finset.range k, (if ((j : ℝ) + 1) / k < v then (1 : ℝ) else 0)

theorem lay_bounds {k : ℕ} (hk : 0 < k) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lay k v ≤ v ∧ v ≤ lay k v + 1 / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set m := ⌈(k : ℝ) * v⌉₊ with hm
  have hmk : m ≤ k := by
    rw [hm, Nat.ceil_le]
    nlinarith
  have hfilt : (Finset.range k).filter (fun j : ℕ => ((j : ℝ) + 1) / k < v) =
      Finset.range (m - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [div_lt_iff₀ hkpos]
    have e : ((j : ℝ) + 1) < v * k ↔ j + 1 < m := by
      rw [hm, Nat.lt_ceil, mul_comm]; push_cast; rfl
    rw [e]
    omega
  have hsum : lay k v = ((m - 1 : ℕ) : ℝ) / k := by
    unfold lay
    rw [← Finset.sum_filter, Finset.sum_const, hfilt, Finset.card_range]
    simp only [nsmul_eq_mul, mul_one]
    ring
  rw [hsum]
  have hle : (k : ℝ) * v ≤ m := Nat.le_ceil _
  have hlt : (m : ℝ) < k * v + 1 := Nat.ceil_lt_add_one (by positivity)
  constructor
  · rw [div_le_iff₀ hkpos]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · simp [h0]; positivity
    · rw [Nat.cast_sub hpos]; push_cast; linarith
  · rw [← add_div, le_div_iff₀ hkpos]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0] at hle; simp at hle ⊢; nlinarith
    · rw [Nat.cast_sub hpos]; push_cast; linarith

theorem lay_measurable (k : ℕ) : Measurable (lay k) := by
  unfold lay
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

/-- integral of the layered function -/
theorem integral_lay {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (k : ℕ) {f : Ξ → ℝ} (hf : Measurable f) :
    ∫ s, lay k (f s) ∂μ =
      (1 / (k : ℝ)) * ∑ j ∈ Finset.range k, μ.real {s | ((j : ℝ) + 1) / k < f s} := by
  unfold lay
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hms : MeasurableSet {s | ((j : ℝ) + 1) / k < f s} := measurableSet_lt measurable_const hf
    rw [← integral_indicator_one hms]
    congr 1
  · intro j _
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun s => ?_)
    · exact (Measurable.ite (measurableSet_lt measurable_const hf) measurable_const
        measurable_const).aestronglyMeasurable
    · split_ifs <;> simp

/-- Two probability measures whose layer probabilities are `T`-close give `T + 1/k`-close
integrals of a `[0,1]`-valued function. -/
theorem integral_close {Ξ : Type} [MeasurableSpace Ξ] (μ ν : Measure Ξ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : Ξ → ℝ} (hf : Measurable f) (hf0 : ∀ s, 0 ≤ f s)
    (hf1 : ∀ s, f s ≤ 1) (T : ℝ) {k : ℕ} (hk : 0 < k)
    (hT : ∀ j ∈ Finset.range k, |μ.real {s | ((j : ℝ) + 1) / k < f s} -
        ν.real {s | ((j : ℝ) + 1) / k < f s}| ≤ T) :
    |∫ s, f s ∂μ - ∫ s, f s ∂ν| ≤ T + 1 / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hint : ∀ (ρ : Measure Ξ) [IsProbabilityMeasure ρ], Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 s)]; exact hf1 s)
  have hintl : ∀ (ρ : Measure Ξ) [IsProbabilityMeasure ρ], Integrable (fun s => lay k (f s)) ρ :=
    fun ρ _ => Integrable.of_bound ((lay_measurable k).comp hf).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun s => by
        have h1 := (lay_bounds hk (hf0 s) (hf1 s)).1
        have h0 : 0 ≤ lay k (f s) := by
          unfold lay
          refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
          split_ifs <;> norm_num
        rw [Real.norm_eq_abs, abs_of_nonneg h0]; linarith [hf1 s])
  have hup : ∀ (ρ : Measure Ξ) [IsProbabilityMeasure ρ],
      ∫ s, lay k (f s) ∂ρ ≤ ∫ s, f s ∂ρ ∧ ∫ s, f s ∂ρ ≤ ∫ s, lay k (f s) ∂ρ + 1 / k := by
    intro ρ _
    constructor
    · exact integral_mono (hintl ρ) (hint ρ) fun s => (lay_bounds hk (hf0 s) (hf1 s)).1
    · have hi2 : Integrable (fun s => lay k (f s) + 1 / (k : ℝ)) ρ :=
        (hintl ρ).add (integrable_const (1 / (k : ℝ)))
      have := integral_mono (hint ρ) hi2 fun s => (lay_bounds hk (hf0 s) (hf1 s)).2
      rw [integral_add (hintl ρ) (integrable_const _)] at this
      simpa using this
  obtain ⟨a1, a2⟩ := hup μ
  obtain ⟨b1, b2⟩ := hup ν
  rw [integral_lay μ k hf] at a1 a2
  rw [integral_lay ν k hf] at b1 b2
  have hsum : |(1 / (k : ℝ)) * ∑ j ∈ Finset.range k, μ.real {s | ((j : ℝ) + 1) / k < f s} -
      (1 / (k : ℝ)) * ∑ j ∈ Finset.range k, ν.real {s | ((j : ℝ) + 1) / k < f s}| ≤ T := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
    calc 1 / (k : ℝ) * |∑ j ∈ Finset.range k, (μ.real {s | ((j : ℝ) + 1) / k < f s} -
          ν.real {s | ((j : ℝ) + 1) / k < f s})|
        ≤ 1 / (k : ℝ) * ∑ j ∈ Finset.range k, T := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hT)
      _ = T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  rw [abs_le] at hsum ⊢
  constructor <;> linarith [hsum.1, hsum.2]

end SolSampleAux

namespace SolSampleAux

/-! ### Lower sets of ℝ -/

theorem lowerset_cases {L : Set ℝ} (hL : IsLowerSet L) :
    L = ∅ ∨ L = Set.univ ∨ ∃ a, (∀ y, y < a → y ∈ L) ∧ (∀ y ∈ L, y ≤ a) := by
  by_cases hne : L.Nonempty
  · by_cases hb : BddAbove L
    · right; right
      refine ⟨sSup L, fun y hy => ?_, fun y hy => le_csSup hb hy⟩
      obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne hy
      exact hL hyz.le hz
    · right; left
      rw [not_bddAbove_iff] at hb
      ext y
      simp only [Set.mem_univ, iff_true]
      obtain ⟨z, hz, hyz⟩ := hb y
      exact hL hyz.le hz
  · left; exact Set.not_nonempty_iff_eq_empty.mp hne

variable {Ξ : Type} [MeasurableSpace Ξ]

theorem lowerset_close (μ ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y : Ξ → ℝ) (D c r : ℝ) (hr : 0 < r)
    (hD : ∀ t, |μ.real {s | Y s ≤ t} - ν.real {s | Y s ≤ t}| ≤ D)
    (hc : ∀ a, ν.real {s | Y s ∈ Set.Icc (a - r) (a + r)} ≤ c)
    (L : Set ℝ) (hL : IsLowerSet L) :
    |μ.real {s | Y s ∈ L} - ν.real {s | Y s ∈ L}| ≤ D + c := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0)
  have hc0 : 0 ≤ c := le_trans measureReal_nonneg (hc 0)
  rcases lowerset_cases hL with h | h | ⟨a, ha1, ha2⟩
  · subst h; simp; linarith
  · subst h; simp; linarith
  · rw [abs_le]
    constructor
    · -- lower bound
      have h1 : μ.real {s | Y s ≤ a - r} ≤ μ.real {s | Y s ∈ L} :=
        measureReal_mono fun s hs => ha1 _ (by simp only [Set.mem_setOf_eq] at hs; linarith)
      have h2 : ν.real {s | Y s ∈ L} ≤
          ν.real ({s | Y s ≤ a - r} ∪ {s | Y s ∈ Set.Icc (a - r) (a + r)}) := by
        refine measureReal_mono fun s hs => ?_
        have := ha2 _ hs
        by_cases h : Y s ≤ a - r
        · exact Or.inl h
        · exact Or.inr ⟨by push_neg at h; linarith, by linarith⟩
      have h3 := measureReal_union_le (μ := ν) {s | Y s ≤ a - r}
        {s | Y s ∈ Set.Icc (a - r) (a + r)}
      have h4 := hD (a - r)
      rw [abs_le] at h4
      linarith [hc a, h4.1]
    · -- upper bound
      have h1 : μ.real {s | Y s ∈ L} ≤ μ.real {s | Y s ≤ a} :=
        measureReal_mono fun s hs => ha2 _ hs
      have h2 : ν.real {s | Y s ≤ a} ≤
          ν.real ({s | Y s ∈ L} ∪ {s | Y s ∈ Set.Icc (a - r) (a + r)}) := by
        refine measureReal_mono fun s hs => ?_
        simp only [Set.mem_setOf_eq] at hs
        rcases lt_or_eq_of_le hs with h | h
        · exact Or.inl (ha1 _ h)
        · exact Or.inr ⟨by linarith, by linarith⟩
      have h3 := measureReal_union_le (μ := ν) {s | Y s ∈ L}
        {s | Y s ∈ Set.Icc (a - r) (a + r)}
      have h4 := hD a
      rw [abs_le] at h4
      linarith [hc a, h4.2]

theorem shift_close (ν : Measure Ξ) [IsProbabilityMeasure ν] (Y : Ξ → ℝ) (c r : ℝ)
    (hc : ∀ a, ν.real {s | Y s ∈ Set.Icc (a - r) (a + r)} ≤ c)
    (L : Set ℝ) (hL : IsLowerSet L) :
    ν.real {s | Y s - r ∈ L} ≤ ν.real {s | Y s + r ∈ L} + c := by
  have hc0 : 0 ≤ c := le_trans measureReal_nonneg (hc 0)
  rcases lowerset_cases hL with h | h | ⟨a, ha1, ha2⟩
  · subst h; simp; linarith
  · subst h; simp; linarith
  · have h2 : ν.real {s | Y s - r ∈ L} ≤
        ν.real ({s | Y s + r ∈ L} ∪ {s | Y s ∈ Set.Icc (a - r) (a + r)}) := by
      refine measureReal_mono fun s hs => ?_
      simp only [Set.mem_setOf_eq] at hs
      have := ha2 _ hs
      by_cases h : Y s + r ∈ L
      · exact Or.inl h
      · right
        have : ¬ (Y s + r < a) := fun h' => h (ha1 _ h')
        push_neg at this
        exact ⟨by linarith, by linarith⟩
    have h3 := measureReal_union_le (μ := ν) {s | Y s + r ∈ L}
      {s | Y s ∈ Set.Icc (a - r) (a + r)}
    linarith [hc a]

theorem perturb_le (μ : Measure Ξ) [IsFiniteMeasure μ] (Z Y : Ξ → ℝ) (B : Set Ξ) (r : ℝ)
    (h : ∀ s ∉ B, |Z s - Y s| ≤ r) (L : Set ℝ) (hL : IsLowerSet L) :
    μ.real {s | Z s ∈ L} ≤ μ.real {s | Y s - r ∈ L} + μ.real B ∧
    μ.real {s | Y s + r ∈ L} ≤ μ.real {s | Z s ∈ L} + μ.real B := by
  constructor
  · have h1 : μ.real {s | Z s ∈ L} ≤ μ.real ({s | Y s - r ∈ L} ∪ B) := by
      refine measureReal_mono fun s hs => ?_
      by_cases hB : s ∈ B
      · exact Or.inr hB
      · left
        have := abs_le.mp (h s hB)
        exact hL (show Y s - r ≤ Z s by linarith) hs
    linarith [measureReal_union_le (μ := μ) {s | Y s - r ∈ L} B]
  · have h1 : μ.real {s | Y s + r ∈ L} ≤ μ.real ({s | Z s ∈ L} ∪ B) := by
      refine measureReal_mono fun s hs => ?_
      by_cases hB : s ∈ B
      · exact Or.inr hB
      · left
        have := abs_le.mp (h s hB)
        exact hL (show Z s ≤ Y s + r by linarith) hs
    linarith [measureReal_union_le (μ := μ) {s | Z s ∈ L} B]

theorem lowerset_perturb_close (μ ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Z Y : Ξ → ℝ) (B : Set Ξ) (D c r : ℝ) (hr : 0 < r)
    (hD : ∀ t, |μ.real {s | Y s ≤ t} - ν.real {s | Y s ≤ t}| ≤ D)
    (hc : ∀ a, ν.real {s | Y s ∈ Set.Icc (a - r) (a + r)} ≤ c)
    (hB : ∀ s ∉ B, |Z s - Y s| ≤ r) (L : Set ℝ) (hL : IsLowerSet L) :
    |μ.real {s | Z s ∈ L} - ν.real {s | Z s ∈ L}| ≤ D + 2 * c + μ.real B + ν.real B := by
  have hL1 : IsLowerSet {y : ℝ | y - r ∈ L} := fun y z hzy hy => hL (by linarith) hy
  have hL2 : IsLowerSet {y : ℝ | y + r ∈ L} := fun y z hzy hy => hL (by linarith) hy
  have e1 := lowerset_close μ ν Y D c r hr hD hc _ hL1
  have e2 := lowerset_close μ ν Y D c r hr hD hc _ hL2
  have s1 := shift_close ν Y c r hc L hL
  obtain ⟨p1, p2⟩ := perturb_le μ Z Y B r hB L hL
  obtain ⟨q1, q2⟩ := perturb_le ν Z Y B r hB L hL
  simp only [Set.mem_setOf_eq] at e1 e2
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-! ### Concentration: an atomless law puts uniformly small mass on short intervals -/

theorem conc_small (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (Y : Ξ → ℝ) (hY : Measurable Y)
    (hna : ∀ a : ℝ, Pξ {s | Y s = a} = 0) :
    ∀ δ > 0, ∃ r > 0, ∀ a : ℝ, Pξ.real {s | Y s ∈ Set.Icc (a - r) (a + r)} < δ := by
  set ν := Pξ.map Y with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hY.aemeasurable
  set F := ProbabilityTheory.cdf ν with hF
  have hmono : Monotone F := ProbabilityTheory.monotone_cdf ν
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro a
    rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
    have hr : Function.rightLim F a = F a :=
      ((ProbabilityTheory.cdf ν).right_continuous a).rightLim_eq
    have hs := (ProbabilityTheory.cdf ν).measure_singleton a
    rw [ProbabilityTheory.measure_cdf, hν, Measure.map_apply hY (measurableSet_singleton a)] at hs
    have hz : Pξ (Y ⁻¹' {a}) = 0 := hna a
    rw [hz] at hs
    have h1 : F a - Function.leftLim F a ≤ 0 := ENNReal.ofReal_eq_zero.mp hs.symm
    have h2 : Function.leftLim F a ≤ F a := hmono.leftLim_le le_rfl
    rw [hr]; linarith
  have hIoc : ∀ x y : ℝ, x ≤ y → ν.real (Set.Ioc x y) = F y - F x := by
    intro x y hxy
    rw [hF, ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
      ← Set.Iic_union_Ioc_eq_Iic hxy,
      measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
    ring
  intro δ hδ
  have hbot : ∀ᶠ t in atBot, F t < δ :=
    (ProbabilityTheory.tendsto_cdf_atBot ν).eventually (gt_mem_nhds hδ)
  have htop : ∀ᶠ t in atTop, 1 - δ < F t :=
    (ProbabilityTheory.tendsto_cdf_atTop ν).eventually (lt_mem_nhds (by linarith))
  obtain ⟨M1, hM1⟩ := eventually_atBot.mp hbot
  obtain ⟨M2, hM2⟩ := eventually_atTop.mp htop
  have huc := (isCompact_Icc (a := M1 - 1) (b := M2 + 1)).uniformContinuousOn_of_continuous
    hFcont.continuousOn
  obtain ⟨r0, hr0, hr0'⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  refine ⟨min (r0 / 4) (1 / 4), by positivity, fun a => ?_⟩
  set r := min (r0 / 4) (1 / 4) with hrdef
  have hr1 : r ≤ r0 / 4 := min_le_left _ _
  have hr2 : r ≤ 1 / 4 := min_le_right _ _
  have hrpos : 0 < r := by positivity
  have key : Pξ.real {s | Y s ∈ Set.Icc (a - r) (a + r)} ≤ F (a + r) - F (a - 2 * r) := by
    have e : Pξ.real {s | Y s ∈ Set.Icc (a - r) (a + r)} = ν.real (Set.Icc (a - r) (a + r)) := by
      rw [hν, map_measureReal_apply hY measurableSet_Icc]; rfl
    rw [e, ← hIoc _ _ (by linarith)]
    exact measureReal_mono (Set.Icc_subset_Ioc_iff (by linarith) |>.mpr ⟨by linarith, le_rfl⟩)
  have hF0 : ∀ t, 0 ≤ F t := ProbabilityTheory.cdf_nonneg ν
  have hF1 : ∀ t, F t ≤ 1 := ProbabilityTheory.cdf_le_one ν
  refine lt_of_le_of_lt key ?_
  by_cases c1 : a + r ≤ M1
  · linarith [hM1 _ c1, hF0 (a - 2 * r)]
  · by_cases c2 : M2 ≤ a - 2 * r
    · linarith [hM2 _ c2, hF1 (a + r)]
    · push_neg at c1 c2
      have hm1 : a - 2 * r ∈ Set.Icc (M1 - 1) (M2 + 1) := ⟨by linarith, by linarith⟩
      have hm2 : a + r ∈ Set.Icc (M1 - 1) (M2 + 1) := ⟨by linarith, by linarith⟩
      have hd : dist (a + r) (a - 2 * r) < r0 := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
      have := hr0' _ hm2 _ hm1 hd
      rw [Real.dist_eq] at this
      linarith [le_abs_self (F (a + r) - F (a - 2 * r))]

/-! ### The smoothing function -/

theorem gam_mem {ε : ℝ} {g : ℝ → ℝ} (h : AdmissibleGamma ε g) (y : ℝ) :
    0 ≤ Gam ε g y ∧ Gam ε g y ≤ 1 := by
  have hε := h.pos
  unfold Gam
  split_ifs with h1 h2
  · norm_num
  · push_neg at h1
    exact h.mapsTo y ⟨h1.le, h2.le⟩
  · norm_num

theorem gam_antitone {ε : ℝ} {g : ℝ → ℝ} (h : AdmissibleGamma ε g) : Antitone (Gam ε g) := by
  intro y z hyz
  have hε := h.pos
  have hm := gam_mem h
  by_cases hz1 : z ≤ -ε
  · have hy1 : y ≤ -ε := le_trans hyz hz1
    simp [Gam, hz1, hy1]
  · by_cases hz2 : z < ε
    · by_cases hy1 : y ≤ -ε
      · have := (hm z).2
        simp only [Gam, hy1, if_true]
        simpa [Gam, hz1, hz2] using this
      · push_neg at hz1 hy1
        have hy2 : y < ε := lt_of_le_of_lt hyz hz2
        simp only [Gam, not_le.mpr hy1, not_le.mpr hz1, if_false, hy2, hz2, if_true]
        exact h.strictAnti.antitoneOn ⟨hy1.le, hy2.le⟩ ⟨hz1.le, hz2.le⟩ hyz
    · have := (hm y).1
      have e : Gam ε g z = 0 := by simp [Gam, hz1, hz2]
      rw [e]; exact this

end SolSampleAux

namespace SolSampleAux

variable {Ξ : Type} [MeasurableSpace Ξ]

theorem gc_emp (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (Z : Ξ → ℝ) (hZ : Measurable Z) :
    ∀ᵐ ω ∂P, ∀ δ > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 1 ≤ N ∧ ∀ t : ℝ,
      |(empM N (fun i => ξ i ω)).real {s | Z s ≤ t} - Pξ.real {s | Z s ≤ t}| < δ := by
  have hidξ : ∀ i, ProbabilityTheory.IdentDistrib (ξ i) (ξ 0) P P := fun i =>
    { aemeasurable_fst := (hξmeas i).aemeasurable
      aemeasurable_snd := (hξmeas 0).aemeasurable
      map_eq := by rw [hξlaw i, hξlaw 0] }
  have hid : ∀ i, ProbabilityTheory.IdentDistrib (fun ω => Z (ξ i ω)) (fun ω => Z (ξ 0 ω)) P P :=
    fun i => (hidξ i).comp hZ
  have hind : ProbabilityTheory.iIndepFun (fun i ω => Z (ξ i ω)) P :=
    hξind.comp (fun _ => Z) (fun _ => hZ)
  have gc := GlivenkoCantelli.glivenko_cantelli P (fun i ω => Z (ξ i ω))
    (fun i => hZ.comp (hξmeas i)) hind hid
  have hcdf : ∀ t, ProbabilityTheory.cdf (P.map (fun ω => Z (ξ 0 ω))) t =
      Pξ.real {s | Z s ≤ t} := by
    intro t
    have : IsProbabilityMeasure (P.map (fun ω => Z (ξ 0 ω))) :=
      Measure.isProbabilityMeasure_map (hZ.comp (hξmeas 0)).aemeasurable
    rw [ProbabilityTheory.cdf_eq_real]
    have hm : P.map (fun ω => Z (ξ 0 ω)) = Pξ.map Z := by
      rw [← hξlaw 0, Measure.map_map hZ (hξmeas 0)]; rfl
    rw [hm, map_measureReal_apply hZ measurableSet_Iic]
    rfl
  filter_upwards [gc] with ω hω
  intro δ hδ
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hω.eventually (gt_mem_nhds hδ))
  refine ⟨max N0 1, fun N hN => ⟨le_trans (le_max_right _ _) hN, fun t => ?_⟩⟩
  have hsup := hN0 N (le_trans (le_max_left _ _) hN)
  have hbdd : BddAbove (Set.range fun x : ℝ =>
      |(((Finset.range N).filter (fun i => Z (ξ i ω) ≤ x)).card : ℝ) / N -
        ProbabilityTheory.cdf (P.map (fun ω => Z (ξ 0 ω))) x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 : (((Finset.range N).filter (fun i => Z (ξ i ω) ≤ x)).card : ℝ) / N ≤ 1 := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]
        exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range N).le
    have h0 : 0 ≤ (((Finset.range N).filter (fun i => Z (ξ i ω) ≤ x)).card : ℝ) / N := by
      positivity
    have := ProbabilityTheory.cdf_nonneg (P.map (fun ω => Z (ξ 0 ω))) x
    have := ProbabilityTheory.cdf_le_one (P.map (fun ω => Z (ξ 0 ω))) x
    rw [abs_le]; constructor <;> linarith
  have hle := le_ciSup hbdd t
  have hemp : (empM N (fun i => ξ i ω)).real {s | Z s ≤ t} =
      (((Finset.range N).filter (fun i => Z (ξ i ω) ≤ t)).card : ℝ) / N := by
    rw [empM_real N _ (measurableSet_le hZ measurable_const), Finset.card_filter]
    push_cast
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    ring
  rw [hemp, ← hcdf t]
  exact lt_of_le_of_lt hle hsup

theorem slln_set (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (B : Set Ξ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, ∀ δ > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 1 ≤ N ∧
      |(empM N (fun i => ξ i ω)).real B - Pξ.real B| < δ := by
  have h := gc_emp Pξ P ξ hξmeas hξind hξlaw (B.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hB)
  have hset : {s | B.indicator (fun _ => (1 : ℝ)) s ≤ 1 / 2} = Bᶜ := by
    ext s
    by_cases hs : s ∈ B <;> simp [hs] <;> norm_num
  filter_upwards [h] with ω hω
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hω δ hδ
  refine ⟨N0, fun N hN => ⟨(hN0 N hN).1, ?_⟩⟩
  have hb := (hN0 N hN).2 (1 / 2)
  rw [hset] at hb
  have hprob : IsProbabilityMeasure (empM N (fun i => ξ i ω)) := empM_prob (hN0 N hN).1 _
  rw [measureReal_compl hB, measureReal_compl hB] at hb
  simp only [probReal_univ] at hb
  rw [abs_sub_comm] at hb
  convert hb using 2
  ring

theorem bad_set {n : ℕ} (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    (C : (Fin n → ℝ) → Ξ → ℝ) (U X : Set (Fin n → ℝ)) (hUX : U ⊆ X)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (xbar : Fin n → ℝ) (hxbar : xbar ∈ U) (r : ℝ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ > 0, ∃ B : Set Ξ, MeasurableSet B ∧ Pξ.real B < δ ∧
      ∀ s ∉ B, ∀ x ∈ U, dist x xbar < ρ → |C x s - C xbar s| ≤ r := by
  obtain ⟨D, hDU, hDc, hUD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace U).exists_countable_dense_subset
  set Nc := toMeasurable Pξ {s | ¬ Continuous (fun x => C x s)} with hNc
  have hNc0 : Pξ Nc = 0 := by
    rw [hNc, measure_toMeasurable]
    exact ae_iff.mp hA32cont
  set Bm : ℕ → Set Ξ := fun m => Nc ∪ ⋃ d ∈ D ∩ {d | dist d xbar < 1 / ((m : ℝ) + 1)},
    {s | r < |C d s - C xbar s|} with hBm
  have hmeas : ∀ m, MeasurableSet (Bm m) := by
    intro m
    refine (measurableSet_toMeasurable _ _).union
      (MeasurableSet.biUnion (hDc.mono Set.inter_subset_left) fun d hd => ?_)
    exact measurableSet_lt measurable_const (continuous_abs.measurable.comp
      ((hA32meas d (hUX (hDU hd.1))).sub (hA32meas xbar (hUX hxbar))))
  have hanti : Antitone Bm := by
    intro m m' hmm' s hs
    rcases hs with hs | hs
    · exact Or.inl hs
    · right
      simp only [Set.mem_iUnion] at hs ⊢
      obtain ⟨d, ⟨hdD, hdd⟩, hds⟩ := hs
      refine ⟨d, ⟨hdD, ?_⟩, hds⟩
      have : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        gcongr
      exact lt_of_lt_of_le hdd this
  have hinter : Pξ (⋂ m, Bm m) = 0 := by
    refine measure_mono_null (fun s hs => ?_) hNc0
    by_contra hsN
    have hcont : Continuous (fun x => C x s) := by
      by_contra hc
      exact hsN (subset_toMeasurable _ _ hc)
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuous_iff.mp hcont xbar r hr
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hρ
    rcases Set.mem_iInter.mp hs m with h | h
    · exact hsN h
    · simp only [Set.mem_iUnion] at h
      obtain ⟨d, ⟨_, hdd⟩, hds⟩ := h
      have := hρ' d (lt_trans hdd hm)
      rw [Real.dist_eq] at this
      simp only [Set.mem_setOf_eq] at hds
      linarith
  have ht := tendsto_measure_iInter_atTop (μ := Pξ) (fun m => (hmeas m).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  refine ⟨1 / ((m : ℝ) + 1), by positivity, Bm m, hmeas m,
    ENNReal.toReal_lt_of_lt_ofReal hm, fun s hs x hx hdx => ?_⟩
  have hsN : s ∉ Nc := fun h => hs (Or.inl h)
  have hcont : Continuous (fun x => C x s) := by
    by_contra hc
    exact hsN (subset_toMeasurable _ _ hc)
  have hS : IsClosed {y | |C y s - C xbar s| ≤ r} :=
    isClosed_le ((continuous_abs.comp (hcont.sub continuous_const))) continuous_const
  have hsub : Metric.ball xbar (1 / ((m : ℝ) + 1)) ∩ D ⊆ {y | |C y s - C xbar s| ≤ r} := by
    intro d ⟨hdb, hdD⟩
    by_contra hd
    simp only [Set.mem_setOf_eq, not_le] at hd
    apply hs
    right
    simp only [Set.mem_iUnion]
    exact ⟨d, ⟨hdD, Metric.mem_ball.mp hdb⟩, hd⟩
  have hxcl : x ∈ closure (Metric.ball xbar (1 / ((m : ℝ) + 1)) ∩ D) :=
    Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball.mpr hdx, hUD hx⟩
  exact closure_minimal hsub hS hxcl

end SolSampleAux

namespace SolSampleAux

variable {Ξ : Type} [MeasurableSpace Ξ]

theorem local_unif {n : ℕ} (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (X : Set (Fin n → ℝ)) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (U : Set (Fin n → ℝ)) (hUX : U ⊆ X) (xbar : Fin n → ℝ) (hxbar : xbar ∈ U)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ∀ᵐ ω ∂P, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ U, dist x xbar < ρ →
      ∀ g : ℝ → ℝ, Antitone g → (∀ y, 0 ≤ g y ∧ g y ≤ 1) →
        |∫ s, g (C x s) ∂(empM N (fun i => ξ i ω)) - ∫ s, g (C x s) ∂Pξ| < η := by
  set δ := η / 8 with hδdef
  have hδ : 0 < δ := by positivity
  have hY : Measurable (C xbar) := hA32meas xbar (hUX hxbar)
  obtain ⟨r, hr, hc⟩ := conc_small Pξ (C xbar) hY (hA31 xbar (hUX hxbar)) δ hδ
  obtain ⟨ρ, hρ, B, hBm, hBP, hBprop⟩ :=
    bad_set Pξ C U X hUX hA32meas hA32cont xbar hxbar r hr δ hδ
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [gc_emp Pξ P ξ hξmeas hξind hξlaw (C xbar) hY,
    slln_set Pξ P ξ hξmeas hξind hξlaw B hBm] with ω hgc hsl
  obtain ⟨N1, h1⟩ := hgc δ hδ
  obtain ⟨N2, h2⟩ := hsl δ hδ
  refine ⟨max N1 N2, fun N hN x hx hdx g hg hg01 => ?_⟩
  have hN1 := h1 N (le_of_max_le_left hN)
  have hN2 := h2 N (le_of_max_le_right hN)
  have hprob : IsProbabilityMeasure (empM N (fun i => ξ i ω)) := empM_prob hN1.1 _
  set μ := empM N (fun i => ξ i ω) with hμ
  set T := δ + 2 * δ + μ.real B + Pξ.real B with hT
  have hTlt : T < η := by
    have := abs_lt.mp hN2.2
    rw [hT]; linarith [this.2]
  have hlow : ∀ L : Set ℝ, IsLowerSet L →
      |μ.real {s | C x s ∈ L} - Pξ.real {s | C x s ∈ L}| ≤ T := fun L hL =>
    lowerset_perturb_close μ Pξ (C x) (C xbar) B δ δ r hr (fun t => (hN1.2 t).le)
      (fun a => (hc a).le) (fun s hs => hBprop s hs x hx hdx) L hL
  have hfm : Measurable (fun s => g (C x s)) := hg.measurable.comp (hA32meas x (hUX hx))
  have hk : ∀ k : ℕ, 0 < k →
      |∫ s, g (C x s) ∂μ - ∫ s, g (C x s) ∂Pξ| ≤ T + 1 / k := by
    intro k hk
    refine integral_close μ Pξ hfm (fun s => (hg01 _).1) (fun s => (hg01 _).2) T hk
      fun j _ => ?_
    have hL : IsLowerSet {y : ℝ | ((j : ℝ) + 1) / k < g y} :=
      fun a b hba ha => lt_of_lt_of_le ha (hg hba)
    exact hlow _ hL
  refine lt_of_le_of_lt ?_ hTlt
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.mpr hcon)
  have := hk (k + 1) (Nat.succ_pos k)
  push_cast at this
  linarith

theorem global_unif {n : ℕ} (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (X : Set (Fin n → ℝ)) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) (η : ℝ) (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ U,
      ∀ g : ℝ → ℝ, Antitone g → (∀ y, 0 ≤ g y ∧ g y ≤ 1) →
        |∫ s, g (C x s) ∂(empM N (fun i => ξ i ω)) - ∫ s, g (C x s) ∂Pξ| < η := by
  refine hU.induction_on (p := fun t => ∀ᵐ ω ∂P, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ t,
      ∀ g : ℝ → ℝ, Antitone g → (∀ y, 0 ≤ g y ∧ g y ≤ 1) →
        |∫ s, g (C x s) ∂(empM N (fun i => ξ i ω)) - ∫ s, g (C x s) ∂Pξ| < η) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun ω => ⟨0, fun N _ x hx => absurd hx (Set.notMem_empty x)⟩
  · intro s t hst ht
    filter_upwards [ht] with ω ⟨N0, h⟩
    exact ⟨N0, fun N hN x hx => h N hN x (hst hx)⟩
  · intro s t hs ht
    filter_upwards [hs, ht] with ω ⟨N1, h1⟩ ⟨N2, h2⟩
    exact ⟨max N1 N2, fun N hN x hx =>
      hx.elim (h1 N (le_of_max_le_left hN) x) (h2 N (le_of_max_le_right hN) x)⟩
  · intro xbar hxbar
    obtain ⟨ρ, hρ, hloc⟩ := local_unif Pξ P ξ hξmeas hξind hξlaw X C hA31 hA32meas hA32cont
      U hUX xbar hxbar η hη
    refine ⟨U ∩ Metric.ball xbar ρ, inter_mem_nhdsWithin U (Metric.ball_mem_nhds xbar hρ), ?_⟩
    filter_upwards [hloc] with ω ⟨N0, h⟩
    exact ⟨N0, fun N hN y hy => h N hN y hy.1 (Metric.mem_ball.mp hy.2)⟩

end SolSampleAux

open SolSampleAux

theorem solution
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (X : Set (Fin n → ℝ)) (hX : IsClosed X) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ U,
      |SmoothCCP.Feasibility.sampleCdf C ε (γ ε) (fun i : Fin N => ξ i ω) 0 x - SmoothCCP.Feasibility.smoothCdf Pξ C ε (γ ε) 0 x| < η := by
  have hall : ∀ m : ℕ, ∀ᵐ ω ∂P, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ U,
      ∀ g : ℝ → ℝ, Antitone g → (∀ y, 0 ≤ g y ∧ g y ≤ 1) →
        |∫ s, g (C x s) ∂(empM N (fun i => ξ i ω)) - ∫ s, g (C x s) ∂Pξ| < 1 / ((m : ℝ) + 1) :=
    fun m => global_unif Pξ P ξ hξmeas hξind hξlaw X C hA31 hA32meas hA32cont U hU hUX _
      (by positivity)
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  intro η hη
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hη
  obtain ⟨N0, hN0⟩ := hω m
  refine ⟨N0, fun N hN ε hε x hx => ?_⟩
  have hadm := hγ ε hε.1
  set g : ℝ → ℝ := fun y => Gam ε (γ ε) (y - 0) with hgdef
  have hanti : Antitone g := fun a b hab => gam_antitone hadm (by linarith)
  have hbd : ∀ y, 0 ≤ g y ∧ g y ≤ 1 := fun y => gam_mem hadm _
  have key := hN0 N hN x hx g hanti hbd
  have hgm : Measurable (fun s => g (C x s)) := hanti.measurable.comp (hA32meas x (hUX hx))
  have e1 : sampleCdf C ε (γ ε) (fun i : Fin N => ξ i ω) 0 x =
      ∫ s, g (C x s) ∂(empM N (fun i => ξ i ω)) := by
    rw [integral_empM N _ hgm]
    unfold sampleCdf
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun i => g (C x (ξ i ω))) N
  have e2 : smoothCdf Pξ C ε (γ ε) 0 x = ∫ s, g (C x s) ∂Pξ := rfl
  rw [e1, e2]
  exact lt_trans key hm
