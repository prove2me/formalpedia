-- Prove2me | solution 1 for SmithRegenerative.Equilibrium.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T04:53:25.290607+00:00
-- url     : https://prove2.me/submissions/46933734-00eb-4633-bebf-d8b8cb3a6971

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess
import Theorems.Thm_SmithRegenerative_Equilibrium_decomposition_3_4_3
import Theorems.Thm_SmithRegenerative_Equilibrium_theorem_A_a
import Theorems.Thm_SmithRegenerative_Equilibrium_theorem_1
import Theorems.Thm_SmithRegenerative_Equilibrium_window_limit_3_4_5
import Theorems.Thm_SmithRegenerative_Equilibrium_tail_limit_3_4_7

set_option autoImplicit false

open MeasureTheory Filter Topology
open QueueingFundamentals.MG1

namespace SmithRegenerative.Equilibrium.T2Glue

open SmithRegenerative.Equilibrium

/-! ## G0: local finiteness of the renewal measure (Chernoff bound; adapted from Sol_pv_b630d11e) -/

noncomputable def expMom (l : ℝ) (ρ : Measure ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(l * x))) ∂ρ

lemma measurable_expden (l : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(l * x)))) := by
  fun_prop

lemma expMom_conv (l : ℝ) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    expMom l (ρ ∗ σ) = expMom l ρ * expMom l σ := by
  unfold expMom
  rw [Measure.lintegral_conv (measurable_expden l)]
  have : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(l * (x + y)))) =
      ENNReal.ofReal (Real.exp (-(l * x))) * ENNReal.ofReal (Real.exp (-(l * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  simp only [this]
  simp only [lintegral_const_mul _ (measurable_expden l)]
  rw [lintegral_mul_const _ (measurable_expden l)]

lemma convPow_isProb (η : Measure ℝ) [IsProbabilityMeasure η] :
    ∀ n, IsProbabilityMeasure (convPow η n)
  | 0 => by rw [convPow]; infer_instance
  | n + 1 => by
      have := convPow_isProb η n
      rw [convPow]; infer_instance

lemma expMom_convPow (η : Measure ℝ) [IsProbabilityMeasure η] (l : ℝ) :
    ∀ n, expMom l (convPow η n) = expMom l η ^ n
  | 0 => by simp [convPow, expMom, lintegral_dirac]
  | n + 1 => by
    have := convPow_isProb η n
    simp only [convPow]
    rw [expMom_conv, expMom_convPow η l n, pow_succ]

lemma meas_Iic_le (l : ℝ) (hl : 0 < l) (ρ : Measure ℝ) (y : ℝ) :
    ρ (Set.Iic y) ≤ ENNReal.ofReal (Real.exp (l * y)) * expMom l ρ := by
  rw [expMom, ← lintegral_const_mul _ (measurable_expden l),
    ← lintegral_indicator_one measurableSet_Iic]
  refine lintegral_mono (fun x => ?_)
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.one_le_ofReal,
      Real.one_le_exp_iff]
    have : x ≤ y := hx
    nlinarith
  · exact bot_le

lemma renewal_Iic_le (K F : Measure ℝ) [SFinite K] [IsProbabilityMeasure F]
    (l : ℝ) (hl : 0 < l) (y : ℝ) :
    renewalMeasure K F (Set.Iic y) ≤
      ENNReal.ofReal (Real.exp (l * y)) * expMom l K * (1 - expMom l F)⁻¹ := by
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Iic, ← ENNReal.tsum_geometric,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have := convPow_isProb F n
  refine (meas_Iic_le l hl _ y).trans (le_of_eq ?_)
  rw [expMom_conv, expMom_convPow F l n, mul_assoc]

/-- A cycle law has positive mass on `(0, ∞)`. -/
lemma cycle_Ioi_pos (F : Measure ℝ) (hF : IsCycleLaw F) : 0 < F (Set.Ioi 0) := by
  obtain ⟨hP, hneg, hne⟩ := hF
  rw [pos_iff_ne_zero]
  intro h0
  apply hne
  ext s hs
  have hc : F {(0:ℝ)}ᶜ = 0 := by
    have : ({(0:ℝ)}ᶜ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h|h)
        · exact h.ne
        · exact h.ne'
    rw [this]; exact measure_union_null hneg h0
  have h1 : F {(0:ℝ)} = 1 := by
    have := measure_add_measure_compl (μ := F) (measurableSet_singleton (0:ℝ))
    rw [hc, add_zero, measure_univ] at this; exact this
  by_cases h : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_mem h, Pi.one_apply]
    apply le_antisymm (prob_le_one)
    rw [← h1]; exact measure_mono (Set.singleton_subset_iff.mpr h)
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h]
    exact measure_mono_null (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; rintro rfl; exact h hx) hc

lemma expMom_lt_one (F : Measure ℝ) (hF : IsCycleLaw F) (l : ℝ) (hl : 0 < l) :
    expMom l F < 1 := by
  have hP := hF.1
  have hneg := hF.2.1
  have hpos := cycle_Ioi_pos F hF
  -- some δ > 0 with F (Ioi δ) > 0
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ 0 < F (Set.Ioi δ) := by
    by_contra hcon
    push_neg at hcon
    have : Set.Ioi (0:ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1)) := by
      ext x; simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    have hnull : F (⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1))) = 0 :=
      measure_iUnion_null (fun n => le_antisymm (hcon _ (by positivity)) bot_le)
    rw [this] at hpos
    exact hpos.ne' hnull
  -- split the integral
  have hae : ∀ᵐ x ∂F, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hneg
  have hbound : ∀ᵐ x ∂F, ENNReal.ofReal (Real.exp (-(l * x))) ≤
      (Set.Ioi δ).indicator (fun _ => ENNReal.ofReal (Real.exp (-(l * δ)))) x +
        (Set.Ioi δ)ᶜ.indicator (fun _ => 1) x := by
    filter_upwards [hae] with x hx
    by_cases hxδ : x ∈ Set.Ioi δ
    · rw [Set.indicator_of_mem hxδ, Set.indicator_of_notMem (by simpa using hxδ), add_zero]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have : δ < x := hxδ
      nlinarith
    · rw [Set.indicator_of_notMem hxδ, Set.indicator_of_mem (by simpa using hxδ), zero_add]
      rw [ENNReal.ofReal_le_one]
      apply Real.exp_le_one_iff.mpr
      nlinarith
  calc expMom l F ≤ ∫⁻ x, ((Set.Ioi δ).indicator (fun _ => ENNReal.ofReal (Real.exp (-(l * δ)))) x +
        (Set.Ioi δ)ᶜ.indicator (fun _ => 1) x) ∂F := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (Real.exp (-(l * δ))) * F (Set.Ioi δ) + F (Set.Ioi δ)ᶜ := by
        rw [lintegral_add_left (Measurable.indicator measurable_const measurableSet_Ioi),
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi.compl]
        simp
    _ < F (Set.Ioi δ) + F (Set.Ioi δ)ᶜ := by
        apply ENNReal.add_lt_add_right (measure_ne_top _ _)
        have hlt : ENNReal.ofReal (Real.exp (-(l * δ))) < 1 := by
          rw [ENNReal.ofReal_lt_one]
          calc Real.exp (-(l * δ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
            _ = 1 := Real.exp_zero
        calc ENNReal.ofReal (Real.exp (-(l * δ))) * F (Set.Ioi δ)
            < 1 * F (Set.Ioi δ) := by
              rw [mul_comm, mul_comm 1]
              exact ENNReal.mul_lt_mul_right hδF.ne' (measure_ne_top _ _) hlt
          _ = F (Set.Ioi δ) := one_mul _
    _ = 1 := by rw [measure_add_measure_compl measurableSet_Ioi, measure_univ]

lemma expMom_le_mass (K : Measure ℝ) (hK0 : K (Set.Iio 0) = 0) (l : ℝ) (hl : 0 ≤ l) :
    expMom l K ≤ K Set.univ := by
  have hae : ∀ᵐ x ∂K, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hK0
  calc expMom l K ≤ ∫⁻ _, 1 ∂K := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        rw [ENNReal.ofReal_le_one]; apply Real.exp_le_one_iff.mpr; nlinarith
    _ = K Set.univ := by simp

lemma renewal_Icc_lt_top (K F : Measure ℝ) [IsFiniteMeasure K] (hK0 : K (Set.Iio 0) = 0)
    (hF : IsCycleLaw F) (t : ℝ) :
    renewalMeasure K F (Set.Icc 0 t) < ⊤ := by
  have := hF.1
  refine lt_of_le_of_lt (measure_mono Set.Icc_subset_Iic_self) ?_
  refine lt_of_le_of_lt (renewal_Iic_le K F 1 one_pos t) ?_
  have h1 := expMom_lt_one F hF 1 one_pos
  have hK : expMom 1 K < ⊤ :=
    lt_of_le_of_lt (expMom_le_mass K hK0 1 zero_le_one) (measure_lt_top _ _)
  have h2 : (1 - expMom 1 F)⁻¹ ≠ ⊤ := by
    rw [Ne, ENNReal.inv_eq_top]; exact (tsub_pos_of_lt h1).ne'
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) (lt_top_iff_ne_top.mpr h2)

end SmithRegenerative.Equilibrium.T2Glue

set_option autoImplicit false

open MeasureTheory Filter Topology
open QueueingFundamentals.MG1

namespace SmithRegenerative.Equilibrium.T2Glue

open SmithRegenerative.Equilibrium

/-! ## G1-G3: the clamp `gt = max 0 (min g (1 - F))` agrees with `g` where it matters -/

section Process
variable {Ω : Type*} [MeasurableSpace Ω]

lemma epoch_zero' (t : ℕ → Ω → ℝ) (ω : Ω) : epoch t 0 ω = t 0 ω := by
  simp [epoch]

lemma epoch_zero_le (t : ℕ → Ω → ℝ) (ht : ∀ i ω, 0 ≤ t i ω) (k : ℕ) (ω : Ω) :
    epoch t 0 ω ≤ epoch t k ω := by
  unfold epoch
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun i _ _ => ht i ω)

lemma renewalCount_pos_iff (t : ℕ → Ω → ℝ) (ht : ∀ i ω, 0 ≤ t i ω) (s : ℝ) (ω : Ω) :
    0 < renewalCount t s ω ↔ t 0 ω ≤ s := by
  unfold renewalCount
  rw [Set.encard_pos]
  constructor
  · rintro ⟨k, hk⟩
    rw [← epoch_zero' t ω]
    exact (epoch_zero_le t ht k ω).trans hk
  · intro h
    exact ⟨0, by show epoch t 0 ω ≤ s; rw [epoch_zero']; exact h⟩

lemma measurable_epoch (t : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (t i)) (k : ℕ) :
    Measurable (epoch t k) := by
  unfold epoch
  exact Finset.measurable_sum _ (fun i _ => hm i)

lemma measurable_lastEpoch (t : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (t i)) (s : ℝ) :
    Measurable (lastEpoch t s) := by
  unfold lastEpoch
  refine Measurable.iSup (fun k => ?_)
  exact Measurable.ite (measurableSet_le (measurable_epoch t hm k) measurable_const)
    (measurable_epoch t hm k) measurable_const

lemma measurableSet_count_pos (t : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (t i))
    (ht : ∀ i ω, 0 ≤ t i ω) (s : ℝ) :
    MeasurableSet {ω | 0 < renewalCount t s ω} := by
  have : {ω | 0 < renewalCount t s ω} = {ω | t 0 ω ≤ s} := by
    ext ω; exact renewalCount_pos_iff t ht s ω
  rw [this]; exact measurableSet_le (hm 0) measurable_const

variable {𝔛 Z : Type*} [MeasurableSpace 𝔛]

/-- G1a: the representation forces `φ_A(s - L_s) ≥ 0` almost surely on `{n_s > 0}`. -/
lemma null_neg (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (s : ℝ) (hs : 0 ≤ s) :
    E.P z {ω | 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}} = 0 := by
  have := E.isProb z
  have hφ := E.measurable_φ A hA
  have hB : MeasurableSet {l : ℝ | E.φ A (s - l) < 0} :=
    measurableSet_lt (hφ.comp (measurable_const.sub measurable_id)) measurable_const
  have hSm : MeasurableSet {ω | 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}} :=
    (measurableSet_count_pos E.t E.measurable_t E.t_nonneg s).inter
      ((measurable_lastEpoch E.t E.measurable_t s) hB)
  have hrep := E.repr z A hA s hs _ hB
  have hint : IntegrableOn (fun ω => E.φ A (s - lastEpoch E.t s ω))
      {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}} (E.P z) :=
    (E.integrable_repr z A hA s hs).mono_set (fun ω hω => hω.1)
  by_contra hne
  have hpos : 0 < ∫ ω in {ω | 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}}, -E.φ A (s - lastEpoch E.t s ω) ∂(E.P z) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have : Function.support (fun ω => -E.φ A (s - lastEpoch E.t s ω)) ∩
          {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}} =
          {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}} := by
        ext ω
        simp only [Set.mem_inter_iff, Function.mem_support]
        constructor
        · exact fun h => h.2
        · intro h
          have h2 : E.φ A (s - lastEpoch E.t s ω) < 0 := h.2
          exact ⟨neg_ne_zero.mpr h2.ne, h⟩
      rw [this]; exact pos_iff_ne_zero.mpr hne
    · filter_upwards [ae_restrict_mem hSm] with ω hω
      have h2 : E.φ A (s - lastEpoch E.t s ω) < 0 := hω.2
      simp only [Pi.zero_apply]; linarith
    · exact hint.neg
  rw [integral_neg] at hpos
  have h0 : 0 ≤ (E.P z {ω | E.x s ω ∈ A ∧ 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | E.φ A (s - l) < 0}}).toReal := ENNReal.toReal_nonneg
  rw [hrep] at h0
  linarith

/-- G1b: the representation forces `φ_A(s - L_s) ≤ 1` almost surely on `{n_s > 0}`. -/
lemma null_gt (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (s : ℝ) (hs : 0 ≤ s) :
    E.P z {ω | 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}} = 0 := by
  have := E.isProb z
  have hφ := E.measurable_φ A hA
  have hB : MeasurableSet {l : ℝ | 1 < E.φ A (s - l)} :=
    measurableSet_lt measurable_const (hφ.comp (measurable_const.sub measurable_id))
  have hSm : MeasurableSet {ω | 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}} :=
    (measurableSet_count_pos E.t E.measurable_t E.t_nonneg s).inter
      ((measurable_lastEpoch E.t E.measurable_t s) hB)
  have hrep := E.repr z A hA s hs _ hB
  have hint : IntegrableOn (fun ω => E.φ A (s - lastEpoch E.t s ω))
      {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}} (E.P z) :=
    (E.integrable_repr z A hA s hs).mono_set (fun ω hω => hω.1)
  have hc : IntegrableOn (fun _ : Ω => (1:ℝ))
      {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}} (E.P z) :=
    (integrable_const (1:ℝ)).integrableOn
  by_contra hne
  have hpos : 0 < ∫ ω in {ω | 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}},
        (E.φ A (s - lastEpoch E.t s ω) - 1) ∂(E.P z) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have : Function.support (fun ω => E.φ A (s - lastEpoch E.t s ω) - 1) ∩
          {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}} =
          {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}} := by
        ext ω
        simp only [Set.mem_inter_iff, Function.mem_support]
        constructor
        · exact fun h => h.2
        · intro h
          have h2 : 1 < E.φ A (s - lastEpoch E.t s ω) := h.2
          exact ⟨sub_ne_zero.mpr h2.ne', h⟩
      rw [this]; exact pos_iff_ne_zero.mpr hne
    · filter_upwards [ae_restrict_mem hSm] with ω hω
      have h2 : 1 < E.φ A (s - lastEpoch E.t s ω) := hω.2
      simp only [Pi.zero_apply]; linarith
    · exact hint.sub hc
  rw [integral_sub hint hc, setIntegral_const, ← hrep, smul_eq_mul, mul_one,
    measureReal_def] at hpos
  have hle := ENNReal.toReal_mono (measure_ne_top (E.P z) _)
    (measure_mono (μ := E.P z) (s := {ω | E.x s ω ∈ A ∧ 0 < renewalCount E.t s ω ∧
      lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}})
      (t := {ω | 0 < renewalCount E.t s ω ∧ lastEpoch E.t s ω ∈ {l : ℝ | 1 < E.φ A (s - l)}})
      (fun ω hω => hω.2))
  linarith

/-- The set of ages where `φ` leaves `[0, 1]`. -/
def badSet (φ : ℝ → ℝ) : Set ℝ := {u | φ u < 0 ∨ 1 < φ u}

lemma measurableSet_badSet (φ : ℝ → ℝ) (hφ : Measurable φ) : MeasurableSet (badSet φ) :=
  (measurableSet_lt hφ measurable_const).union (measurableSet_lt measurable_const hφ)

/-- The age process `s - L_s`, as an equilibrium process with the single state set `N`. -/
noncomputable def ageProc (E : EquilibriumProcess Ω 𝔛 Z) (N : Set ℝ) (hN : MeasurableSet N) :
    EquilibriumProcess Ω ℝ Z where
  P := E.P
  isProb := E.isProb
  F := E.F
  cycleLaw := E.cycleLaw
  K := E.K
  t := E.t
  measurable_t := E.measurable_t
  t_nonneg := E.t_nonneg
  indep := E.indep
  law_cycle := E.law_cycle
  law_delay := E.law_delay
  x := fun s ω => s - lastEpoch E.t s ω
  measurable_x := fun s => measurable_const.sub (measurable_lastEpoch E.t E.measurable_t s)
  𝒜 := {N}
  measurableSet_of_mem := fun A hA => by rw [Set.mem_singleton_iff.mp hA]; exact hN
  φ := fun _ => N.indicator 1
  measurable_φ := fun _ _ => measurable_const.indicator hN
  integrable_repr := by
    intro z A _ s _
    have := E.isProb z
    refine Integrable.integrableOn (Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_)
    · exact ((measurable_const.indicator hN).comp
        (measurable_const.sub (measurable_lastEpoch E.t E.measurable_t s))).aestronglyMeasurable
    · exact Eventually.of_forall (fun ω => by
        simp only [Set.indicator, Pi.one_apply]
        split_ifs <;> simp)
  repr := by
    intro z A hA s _ B _
    rw [Set.mem_singleton_iff.mp hA]
    have hT : MeasurableSet {ω | s - lastEpoch E.t s ω ∈ N} :=
      (measurable_const.sub (measurable_lastEpoch E.t E.measurable_t s)) hN
    have hfun : (fun ω => N.indicator (1 : ℝ → ℝ) (s - lastEpoch E.t s ω)) =
        {ω | s - lastEpoch E.t s ω ∈ N}.indicator (fun _ => (1:ℝ)) := by
      funext ω; rfl
    show _ = ∫ ω in _, N.indicator (1 : ℝ → ℝ) (s - lastEpoch E.t s ω) ∂(E.P z)
    rw [hfun, setIntegral_indicator hT, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    congr 2
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto

/-- G2: the renewal integral of `1_bad · (1 - F)` vanishes. -/
lemma bad_integral_zero (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ τ in Set.Icc 0 t, (badSet (E.φ A)).indicator 1 (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
      ∂(renewalMeasure (E.K z) E.F) = 0 := by
  have := E.isProb z
  have hN := measurableSet_badSet (E.φ A) (E.measurable_φ A hA)
  have hdec : (E.P z {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A)}).toReal =
      (E.P z {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A) ∧ t < E.t 0 ω}).toReal +
        ∫ τ in Set.Icc 0 t, (badSet (E.φ A)).indicator 1 (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
          ∂(renewalMeasure (E.K z) E.F) :=
    decomposition_3_4_3 (ageProc E _ hN) z (badSet (E.φ A)) (Set.mem_singleton _) t ht
  have hsub : {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A)} ⊆
      {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A) ∧ t < E.t 0 ω} ∪
      ({ω | 0 < renewalCount E.t t ω ∧ lastEpoch E.t t ω ∈ {l : ℝ | E.φ A (t - l) < 0}} ∪
       {ω | 0 < renewalCount E.t t ω ∧ lastEpoch E.t t ω ∈ {l : ℝ | 1 < E.φ A (t - l)}}) := by
    intro ω hω
    by_cases h0 : t < E.t 0 ω
    · exact Or.inl ⟨hω, h0⟩
    · have hn : 0 < renewalCount E.t t ω :=
        (renewalCount_pos_iff E.t E.t_nonneg t ω).mpr (not_lt.mp h0)
      have hω' : E.φ A (t - lastEpoch E.t t ω) < 0 ∨ 1 < E.φ A (t - lastEpoch E.t t ω) := hω
      rcases hω' with h | h
      · exact Or.inr (Or.inl ⟨hn, h⟩)
      · exact Or.inr (Or.inr ⟨hn, h⟩)
  have hle : E.P z {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A)} ≤
      E.P z {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A) ∧ t < E.t 0 ω} := by
    calc _ ≤ E.P z _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ E.P z {ω | t - lastEpoch E.t t ω ∈ badSet (E.φ A) ∧ t < E.t 0 ω} + (0 + 0) := by
        gcongr
        refine (measure_union_le _ _).trans (le_of_eq ?_)
        rw [null_neg E z A hA t ht, null_gt E z A hA t ht]
      _ = _ := by simp
  have hle' := ENNReal.toReal_mono (measure_ne_top _ _) hle
  have hI0 : 0 ≤ ∫ τ in Set.Icc 0 t, (badSet (E.φ A)).indicator 1 (t - τ) *
      (E.F (Set.Ioi (t - τ))).toReal ∂(renewalMeasure (E.K z) E.F) :=
    setIntegral_nonneg measurableSet_Icc (fun τ _ =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => by simp) _) ENNReal.toReal_nonneg)
  linarith

end Process

/-! ## G3: a function killed by every renewal integral vanishes Lebesgue-a.e. on `[0, ∞)` -/

lemma ae_zero_of_conv_zero (K : Measure ℝ) [SFinite K] (hK : K (Set.Iio 0) = 0)
    (hK1 : K Set.univ ≠ 0) (hh : ℝ → ENNReal) (hhm : Measurable hh)
    (h0 : ∀ t, 0 ≤ t → ∫⁻ τ in Set.Icc 0 t, hh (t - τ) ∂K = 0) :
    ∀ᵐ v ∂(volume.restrict (Set.Ici (0:ℝ))), hh v = 0 := by
  have hae : ∀ᵐ τ ∂K, 0 ≤ τ := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hK
  have hrow : ∀ t : ℝ, ∫⁻ τ, (Set.Ici (0:ℝ)).indicator hh (t - τ) ∂K = 0 := by
    intro t
    have heq : (fun τ => (Set.Ici (0:ℝ)).indicator hh (t - τ)) =ᵐ[K]
        (Set.Icc 0 t).indicator (fun τ => hh (t - τ)) := by
      filter_upwards [hae] with τ hτ
      by_cases htτ : τ ≤ t
      · rw [Set.indicator_of_mem (show t - τ ∈ Set.Ici (0:ℝ) by simp; linarith),
          Set.indicator_of_mem (show τ ∈ Set.Icc 0 t from ⟨hτ, htτ⟩)]
      · rw [Set.indicator_of_notMem (show t - τ ∉ Set.Ici (0:ℝ) by simp; linarith),
          Set.indicator_of_notMem (show τ ∉ Set.Icc 0 t from fun h => htτ h.2)]
    rw [lintegral_congr_ae heq, lintegral_indicator measurableSet_Icc]
    by_cases ht : 0 ≤ t
    · exact h0 t ht
    · rw [Set.Icc_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure]
  have hm2 : Measurable (Function.uncurry fun (t τ : ℝ) => (Set.Ici (0:ℝ)).indicator hh (t - τ)) :=
    (hhm.indicator measurableSet_Ici).comp (measurable_fst.sub measurable_snd)
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := K) hm2.aemeasurable
  simp only [hrow, lintegral_zero] at hswap
  have hinner : ∀ τ : ℝ, ∫⁻ t, (Set.Ici (0:ℝ)).indicator hh (t - τ) =
      ∫⁻ u, (Set.Ici (0:ℝ)).indicator hh u := fun τ =>
    lintegral_sub_right_eq_self ((Set.Ici (0:ℝ)).indicator hh) τ
  simp only [hinner, lintegral_const] at hswap
  rcases mul_eq_zero.mp hswap.symm with hc | hc
  · rw [lintegral_indicator measurableSet_Ici] at hc
    exact (lintegral_eq_zero_iff hhm).mp hc
  · exact absurd hc hK1

end SmithRegenerative.Equilibrium.T2Glue

namespace SmithRegenerative.Equilibrium.T2Glue

open SmithRegenerative.Equilibrium

/-! ## Main glue: the clamp, the a.e. identities, and the case split -/

noncomputable def Fb (F : Measure ℝ) (v : ℝ) : ℝ := (F (Set.Ioi v)).toReal

lemma Fb_antitone (F : Measure ℝ) [IsFiniteMeasure F] : Antitone (Fb F) := fun _ _ hvw =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hvw))

lemma Fb_measurable (F : Measure ℝ) [IsFiniteMeasure F] : Measurable (Fb F) :=
  (Fb_antitone F).measurable

lemma Fb_nonneg (F : Measure ℝ) (v : ℝ) : 0 ≤ Fb F v := ENNReal.toReal_nonneg

lemma Fb_le_one (F : Measure ℝ) [IsProbabilityMeasure F] (v : ℝ) : Fb F v ≤ 1 := by
  unfold Fb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

lemma tendsto_Ioi_zero (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun t : ℝ => (μ (Set.Ioi t)).toReal) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun t : ℝ => Set.Ioi t)
    (fun _ => measurableSet_Ioi.nullMeasurableSet)
    (fun a b hab => Set.Ioi_subset_Ioi hab) ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ t : ℝ, Set.Ioi t) = ∅ :=
    Set.eq_empty_of_forall_notMem (fun x hx => lt_irrefl x (Set.mem_iInter.mp hx x))
  rw [hI, measure_empty] at h
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

lemma Fb_tendsto (F : Measure ℝ) [IsFiniteMeasure F] : Tendsto (Fb F) atTop (𝓝 0) :=
  tendsto_Ioi_zero F

/-- The clamp `max 0 (min g (1 - F))` of `g = φ · (1 - F)`. -/
noncomputable def clampG (φ : ℝ → ℝ) (F : Measure ℝ) (v : ℝ) : ℝ :=
  max 0 (min (φ v * Fb F v) (Fb F v))

lemma clampG_nonneg (φ : ℝ → ℝ) (F : Measure ℝ) (v : ℝ) : 0 ≤ clampG φ F v := le_max_left _ _

lemma clampG_le_Fb (φ : ℝ → ℝ) (F : Measure ℝ) (v : ℝ) : clampG φ F v ≤ Fb F v :=
  max_le (Fb_nonneg F v) (min_le_right _ _)

lemma clampG_measurable (φ : ℝ → ℝ) (hφ : Measurable φ) (F : Measure ℝ) [IsFiniteMeasure F] :
    Measurable (clampG φ F) :=
  measurable_const.max ((hφ.mul (Fb_measurable F)).min (Fb_measurable F))

lemma clampG_eq (φ : ℝ → ℝ) (F : Measure ℝ) (v : ℝ)
    (h : (badSet φ).indicator 1 v * Fb F v = 0) : φ v * Fb F v = clampG φ F v := by
  unfold clampG
  have hF := Fb_nonneg F v
  by_cases hb : v ∈ badSet φ
  · rw [Set.indicator_of_mem hb, Pi.one_apply, one_mul] at h
    rw [h]; simp
  · have hb' : ¬ (φ v < 0 ∨ 1 < φ v) := hb
    push_neg at hb'
    have h1 : 0 ≤ φ v * Fb F v := mul_nonneg hb'.1 hF
    have h2 : φ v * Fb F v ≤ Fb F v := by nlinarith [hb'.2]
    rw [min_eq_left h2, max_eq_right h1]

section Proc
variable {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]

lemma K_prob (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) : IsProbabilityMeasure (E.K z) := by
  rw [← E.law_delay z]
  have := E.isProb z
  exact Measure.isProbabilityMeasure_map (E.measurable_t 0).aemeasurable

lemma K_neg (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) : E.K z (Set.Iio 0) = 0 := by
  rw [← E.law_delay z, Measure.map_apply (E.measurable_t 0) measurableSet_Iio]
  rw [show (E.t 0) ⁻¹' Set.Iio 0 = ∅ from Set.eq_empty_of_forall_notMem
    (fun ω h => (not_lt.mpr (E.t_nonneg 0 ω)) h), measure_empty]

lemma bad_integrable (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜) (t : ℝ) :
    Integrable (fun τ => (badSet (E.φ A)).indicator 1 (t - τ) * Fb E.F (t - τ))
      ((renewalMeasure (E.K z) E.F).restrict (Set.Icc 0 t)) := by
  have := K_prob E z
  have := E.cycleLaw.1
  have hfin := renewal_Icc_lt_top (E.K z) E.F (K_neg E z) E.cycleLaw t
  have : IsFiniteMeasure ((renewalMeasure (E.K z) E.F).restrict (Set.Icc 0 t)) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  refine Integrable.mono' (integrable_const (1:ℝ)) ?_ (Eventually.of_forall fun τ => ?_)
  · exact (((measurable_const.indicator (measurableSet_badSet _ (E.measurable_φ A hA))).mul
      (Fb_measurable E.F)).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · have h1 := Fb_le_one E.F (t - τ)
    have h0 := Fb_nonneg E.F (t - τ)
    simp only [Set.indicator, Pi.one_apply]
    split_ifs
    · rw [one_mul, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    · simp

/-- `g(t - τ) = clamp(t - τ)` for `H_K`-a.e. `τ ∈ [0, t]`. -/
lemma glue_H_ae (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ τ ∂((renewalMeasure (E.K z) E.F).restrict (Set.Icc 0 t)),
      E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal = clampG (E.φ A) E.F (t - τ) := by
  have hnn : 0 ≤ᵐ[(renewalMeasure (E.K z) E.F).restrict (Set.Icc 0 t)]
      (fun τ => (badSet (E.φ A)).indicator 1 (t - τ) * Fb E.F (t - τ)) :=
    Eventually.of_forall (fun τ => mul_nonneg (Set.indicator_nonneg (fun _ _ => by simp) _)
      (Fb_nonneg _ _))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (bad_integrable E z A hA t)).mp
    (bad_integral_zero E z A hA t ht)
  filter_upwards [hae] with τ hτ
  exact clampG_eq (E.φ A) E.F (t - τ) hτ

/-- `g = clamp` Lebesgue-a.e. on `(0, ∞)`. -/
lemma glue_L_ae (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜) :
    ∀ᵐ v ∂(volume.restrict (Set.Ioi (0:ℝ))),
      E.φ A v * (E.F (Set.Ioi v)).toReal = clampG (E.φ A) E.F v := by
  have hKp := K_prob E z
  have := E.cycleLaw.1
  set hh : ℝ → ENNReal := fun v => ENNReal.ofReal ((badSet (E.φ A)).indicator 1 v * Fb E.F v)
    with hhdef
  have hhm : Measurable hh := ENNReal.measurable_ofReal.comp
    ((measurable_const.indicator (measurableSet_badSet _ (E.measurable_φ A hA))).mul
      (Fb_measurable E.F))
  have hle : E.K z ≤ renewalMeasure (E.K z) E.F := by
    have h := Measure.le_sum (fun n : ℕ => (E.K z).conv (convPow E.F n)) 0
    simpa [convPow, renewalMeasure] using h
  have h0 : ∀ t, 0 ≤ t → ∫⁻ τ in Set.Icc 0 t, hh (t - τ) ∂(E.K z) = 0 := by
    intro t ht
    refine le_antisymm ?_ bot_le
    have hnn : 0 ≤ᵐ[(renewalMeasure (E.K z) E.F).restrict (Set.Icc 0 t)]
        (fun τ => (badSet (E.φ A)).indicator 1 (t - τ) * Fb E.F (t - τ)) :=
      Eventually.of_forall (fun τ => mul_nonneg (Set.indicator_nonneg (fun _ _ => by simp) _)
        (Fb_nonneg _ _))
    calc ∫⁻ τ in Set.Icc 0 t, hh (t - τ) ∂(E.K z)
        ≤ ∫⁻ τ in Set.Icc 0 t, hh (t - τ) ∂(renewalMeasure (E.K z) E.F) :=
          lintegral_mono' (Measure.restrict_mono subset_rfl hle) le_rfl
      _ = ENNReal.ofReal (∫ τ in Set.Icc 0 t, (badSet (E.φ A)).indicator 1 (t - τ) *
            Fb E.F (t - τ) ∂(renewalMeasure (E.K z) E.F)) :=
          (ofReal_integral_eq_lintegral_ofReal (bad_integrable E z A hA t) hnn).symm
      _ = 0 := by
          have := bad_integral_zero E z A hA t ht
          unfold Fb; rw [this, ENNReal.ofReal_zero]
  have hK1 : E.K z Set.univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  have hae := ae_zero_of_conv_zero (E.K z) (K_neg E z) hK1 hh hhm h0
  rw [ae_restrict_iff' measurableSet_Ici] at hae
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hae] with v hv hvpos
  apply clampG_eq
  have h1 := hv (Set.mem_Ici.mpr (le_of_lt hvpos))
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp h1)
    (mul_nonneg (Set.indicator_nonneg (fun _ _ => by simp) _) (Fb_nonneg _ _))

lemma first_term_tendsto (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) :
    Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A ∧ t < E.t 0 ω}).toReal) atTop (𝓝 0) := by
  have := E.isProb z
  have := K_prob E z
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_Ioi_zero (E.K z))
    (fun t => ENNReal.toReal_nonneg) (fun t => ?_)
  rw [← E.law_delay z, Measure.map_apply (E.measurable_t 0) measurableSet_Ioi]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω hω => hω.2))

lemma reduce_to_renewal (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (L : ℝ) (hlim : Tendsto (fun t : ℝ => ∫ τ in Set.Icc 0 t, clampG (E.φ A) E.F (t - τ)
      ∂(renewalMeasure (E.K z) E.F)) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop (𝓝 L) := by
  have h := (first_term_tendsto E z A).add hlim
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [decomposition_3_4_3 E z A hA t ht, integral_congr_ae (glue_H_ae E z A hA t ht)]

end Proc

/-- Layer cake: `∫_{(0,∞)} (1 - F) = μ₁`, so `1 - F ∈ L¹(0, ∞)` when `μ₁ < ∞`. -/
lemma Fb_integrableOn (F : Measure ℝ) (hF : IsCycleLaw F) (hμ : mean F < ⊤) :
    IntegrableOn (Fb F) (Set.Ioi 0) := by
  have := hF.1
  have hae : 0 ≤ᵐ[F] (fun x : ℝ => x) := by
    have hs : {a : ℝ | ¬ (0:ℝ) ≤ a} = Set.Iio 0 := by ext; simp
    show ∀ᵐ x ∂F, (0:ℝ) ≤ x
    rw [ae_iff, hs]; exact hF.2.1
  have hlc := lintegral_eq_lintegral_meas_lt F hae measurable_id.aemeasurable
  have hm : Measurable (fun v : ℝ => F (Set.Ioi v)) :=
    Antitone.measurable (fun _ _ hvw => measure_mono (Set.Ioi_subset_Ioi hvw))
  have hfin : ∫⁻ v in Set.Ioi 0, F (Set.Ioi v) ≠ ⊤ := by
    have : ∫⁻ v in Set.Ioi 0, F (Set.Ioi v) = mean F := by
      rw [mean, hlc]; rfl
    rw [this]; exact hμ.ne
  exact integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin

end SmithRegenerative.Equilibrium.T2Glue

namespace SmithRegenerative.Equilibrium.T2Glue

open SmithRegenerative.Equilibrium

lemma clampG_bdd (φ : ℝ → ℝ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → |clampG φ F v| ≤ C :=
  ⟨1, fun v _ => by
    rw [abs_of_nonneg (clampG_nonneg _ _ _)]
    exact (clampG_le_Fb _ _ _).trans (Fb_le_one _ _)⟩

lemma clampG_zero (φ : ℝ → ℝ) (F : Measure ℝ) (v : ℝ) (h : φ v * Fb F v ≤ 0) :
    clampG φ F v = 0 :=
  max_eq_left ((min_le_left _ _).trans h)

lemma nonpos_of_monotone_integrable (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Ioi 0))
    (hint : IntegrableOn g (Set.Ioi 0)) (v : ℝ) (hv : 0 < v) : g v ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have h1 : IntegrableOn g (Set.Ioi v) := hint.mono_set (Set.Ioi_subset_Ioi hv.le)
  have h2 : IntegrableOn (fun _ => g v) (Set.Ioi v) := by
    refine Integrable.mono' h1 aestronglyMeasurable_const ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall (fun w hw => by
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      exact hg (Set.mem_Ioi.mpr hv) (Set.mem_Ioi.mpr (hv.trans hw)) (le_of_lt hw))
  rw [integrableOn_const_iff] at h2
  rcases h2 with h | h
  · simp at h; linarith
  · simp [Real.volume_Ioi] at h

section Final
variable {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]

lemma limit_value (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜) :
    ∫ v in Set.Ioi 0, clampG (E.φ A) E.F v =
      ∫ v in Set.Ioi 0, E.φ A v * (E.F (Set.Ioi v)).toReal :=
  (integral_congr_ae (glue_L_ae E z A hA)).symm

lemma bv_case (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (hper : IsAperiodic E.F) (hμ : mean E.F < ⊤)
    (hbv : ∀ b : ℝ, BoundedVariationOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal)
      (Set.Icc 0 b)) :
    Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop
      (𝓝 ((mean E.F).toReal⁻¹ * ∫ v in Set.Ioi 0, E.φ A v * (E.F (Set.Ioi v)).toReal)) := by
  have hKp := K_prob E z
  have hFp := E.cycleLaw.1
  apply reduce_to_renewal E z A hA
  rw [← limit_value E z A hA]
  have hm0 : 0 ≤ (mean E.F).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hgm : Measurable (clampG (E.φ A) E.F) := clampG_measurable _ (E.measurable_φ A hA) _
  have hFbi : IntegrableOn (fun v => (E.F (Set.Ioi v)).toReal) (Set.Ioi 0) :=
    Fb_integrableOn E.F E.cycleLaw hμ
  have hgti : IntegrableOn (clampG (E.φ A) E.F) (Set.Ioi 0) :=
    Integrable.mono' hFbi hgm.aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (clampG_nonneg _ _ _)]; exact clampG_le_Fb _ _ _)
  have htl := tail_limit_3_4_7 E z hper hμ
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Δ, hΔ, hΔ'⟩ := htl.2 (ε / 4) (by linarith)
  have hτ := hΔ' Δ le_rfl
  have hW := window_limit_3_4_5 E z A hA hper hμ Δ hΔ hbv
  have hT := htl.1 Δ hΔ
  rw [Metric.tendsto_atTop] at hW hT
  obtain ⟨T1, hT1⟩ := hW (ε / 4) (by linarith)
  obtain ⟨T2, hT2⟩ := hT (ε / 4) (by linarith)
  refine ⟨max (max T1 T2) Δ, fun t ht => ?_⟩
  have ht1 : T1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht2 : T2 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htΔ : Δ ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 ≤ t := hΔ.le.trans htΔ
  specialize hT1 t ht1
  specialize hT2 t ht2
  rw [Real.dist_eq] at hT1 hT2 ⊢
  -- local finiteness and integrability on `[0, t]`
  have hfin := renewal_Icc_lt_top (E.K z) E.F (K_neg E z) E.cycleLaw t
  have : IsFiniteMeasure ((renewalMeasure (E.K z) E.F).restrict (Set.Icc 0 t)) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  have hb1 : IntegrableOn (fun τ => clampG (E.φ A) E.F (t - τ)) (Set.Icc 0 t)
      (renewalMeasure (E.K z) E.F) := by
    refine Integrable.mono' (integrable_const (1:ℝ))
      (hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (clampG_nonneg _ _ _)]
    exact (clampG_le_Fb _ _ _).trans (Fb_le_one _ _)
  have hb2 : IntegrableOn (fun τ => (E.F (Set.Ioi (t - τ))).toReal) (Set.Icc 0 t)
      (renewalMeasure (E.K z) E.F) := by
    refine Integrable.mono' (integrable_const (1:ℝ))
      ((Fb_measurable E.F).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact Fb_le_one E.F (t - τ)
  have hsubA : Set.Ico 0 (t - Δ) ⊆ Set.Icc 0 t := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hsubB : Set.Icc (t - Δ) t ⊆ Set.Icc 0 t := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hsubC : Set.Icc 0 (t - Δ) ⊆ Set.Icc 0 t := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  -- split `[0, t] = [0, t - Δ) ∪ [t - Δ, t]`
  have hsplit : ∫ τ in Set.Icc 0 t, clampG (E.φ A) E.F (t - τ) ∂(renewalMeasure (E.K z) E.F) =
      (∫ τ in Set.Ico 0 (t - Δ), clampG (E.φ A) E.F (t - τ) ∂(renewalMeasure (E.K z) E.F)) +
      ∫ τ in Set.Icc (t - Δ) t, clampG (E.φ A) E.F (t - τ) ∂(renewalMeasure (E.K z) E.F) := by
    have hu := Set.Ico_union_Icc_eq_Icc (show (0:ℝ) ≤ t - Δ by linarith)
      (show t - Δ ≤ t by linarith)
    conv_lhs => rw [← hu]
    exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => absurd hx'.1 (not_le.mpr hx.2))
      measurableSet_Icc (hb1.mono_set hsubA) (hb1.mono_set hsubB)
  have hWeq : ∫ τ in Set.Icc (t - Δ) t, E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
      ∂(renewalMeasure (E.K z) E.F) =
      ∫ τ in Set.Icc (t - Δ) t, clampG (E.φ A) E.F (t - τ) ∂(renewalMeasure (E.K z) E.F) :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsubB (glue_H_ae E z A hA t ht0))
  have hR0 : 0 ≤ ∫ τ in Set.Ico 0 (t - Δ), clampG (E.φ A) E.F (t - τ)
      ∂(renewalMeasure (E.K z) E.F) :=
    setIntegral_nonneg measurableSet_Ico (fun τ _ => clampG_nonneg _ _ _)
  have hR1 : ∫ τ in Set.Ico 0 (t - Δ), clampG (E.φ A) E.F (t - τ)
      ∂(renewalMeasure (E.K z) E.F) ≤
      ∫ τ in Set.Ico 0 (t - Δ), (E.F (Set.Ioi (t - τ))).toReal ∂(renewalMeasure (E.K z) E.F) :=
    setIntegral_mono_on (hb1.mono_set hsubA) (hb2.mono_set hsubA) measurableSet_Ico
      (fun τ _ => clampG_le_Fb _ _ _)
  have hR2 : ∫ τ in Set.Ico 0 (t - Δ), (E.F (Set.Ioi (t - τ))).toReal
      ∂(renewalMeasure (E.K z) E.F) ≤
      ∫ τ in Set.Icc 0 (t - Δ), (E.F (Set.Ioi (t - τ))).toReal ∂(renewalMeasure (E.K z) E.F) :=
    setIntegral_mono_set (hb2.mono_set hsubC)
      (Eventually.of_forall fun τ => ENNReal.toReal_nonneg)
      Set.Ico_subset_Icc_self.eventuallyLE
  -- the limit side: `∫_{(0,∞)} = ∫_{(0,Δ]} + ∫_{(Δ,∞)}`
  have hsubD : Set.Ioc 0 Δ ⊆ Set.Ioi (0:ℝ) := fun x hx => hx.1
  have hsubE : Set.Ioi Δ ⊆ Set.Ioi (0:ℝ) := Set.Ioi_subset_Ioi hΔ.le
  have hLsplit : ∫ v in Set.Ioi 0, clampG (E.φ A) E.F v =
      (∫ v in Set.Ioc 0 Δ, clampG (E.φ A) E.F v) + ∫ v in Set.Ioi Δ, clampG (E.φ A) E.F v := by
    conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi hΔ.le]
    exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'))
      measurableSet_Ioi (hgti.mono_set hsubD) (hgti.mono_set hsubE)
  have hweq : ∫ v in Set.Ioc 0 Δ, E.φ A v * (E.F (Set.Ioi v)).toReal =
      ∫ v in Set.Ioc 0 Δ, clampG (E.φ A) E.F v :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsubD (glue_L_ae E z A hA))
  have hX0 : 0 ≤ ∫ v in Set.Ioi Δ, clampG (E.φ A) E.F v :=
    setIntegral_nonneg measurableSet_Ioi (fun v _ => clampG_nonneg _ _ _)
  have hX1 : ∫ v in Set.Ioi Δ, clampG (E.φ A) E.F v ≤
      ∫ v in Set.Ioi Δ, (E.F (Set.Ioi v)).toReal :=
    setIntegral_mono_on (hgti.mono_set hsubE) (hFbi.mono_set hsubE) measurableSet_Ioi
      (fun v _ => clampG_le_Fb _ _ _)
  have hmX0 := mul_nonneg hm0 hX0
  have hmX1 := mul_le_mul_of_nonneg_left hX1 hm0
  rw [hWeq, hweq] at hT1
  rw [hsplit, hLsplit, mul_add]
  rw [abs_lt] at hT1 hT2 ⊢
  constructor <;> linarith [hT1.1, hT1.2, hT2.1, hT2.2]

end Final

end SmithRegenerative.Equilibrium.T2Glue

open SmithRegenerative.Equilibrium SmithRegenerative.Equilibrium.T2Glue MeasureTheory Filter Topology in
theorem solution {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (hper : IsAperiodic E.F)
    (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (hiv :
      (IntegrableOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Ioi 0) ∧
        (MonotoneOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Ioi 0) ∨
          AntitoneOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Ioi 0))) ∨
      (mean E.F < ⊤ ∧
        ((∀ b : ℝ, BoundedVariationOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal)
            (Set.Icc 0 b)) ∨
          InClassS E.F))) :
    (mean E.F = ⊤ →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop (𝓝 0)) ∧
    (mean E.F ≠ ⊤ →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop
        (𝓝 ((mean E.F).toReal⁻¹ * ∫ v in Set.Ioi 0, E.φ A v * (E.F (Set.Ioi v)).toReal))) := by
  have hKp := K_prob E z
  have hFp := E.cycleLaw.1
  have hdelay : IsDelayLaw (E.K z) := ⟨K_neg E z, prob_le_one⟩
  have hgm := clampG_measurable (E.φ A) (E.measurable_φ A hA) E.F
  have hKu : (E.K z Set.univ).toReal = 1 := by rw [measure_univ, ENNReal.toReal_one]
  have fin : Tendsto (fun t : ℝ => ∫ s in Set.Icc 0 t, clampG (E.φ A) E.F (t - s)
      ∂(renewalMeasure (E.K z) E.F)) atTop
      (𝓝 ((E.K z Set.univ).toReal / (mean E.F).toReal *
        ∫ v in Set.Ioi 0, clampG (E.φ A) E.F v)) →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop
        (𝓝 ((mean E.F).toReal⁻¹ * ∫ v in Set.Ioi 0, E.φ A v * (E.F (Set.Ioi v)).toReal)) := by
    intro h
    rw [hKu, limit_value E z A hA, one_div] at h
    exact reduce_to_renewal E z A hA _ h
  rcases hiv with ⟨hint, hmono⟩ | ⟨hμ, hbv | hS⟩
  · have hintc : IntegrableOn (clampG (E.φ A) E.F) (Set.Ioi 0) :=
      hint.congr (glue_L_ae E z A hA)
    have hanti : AntitoneOn (clampG (E.φ A) E.F) (Set.Ioi 0) := by
      rcases hmono with hmo | han
      · have hz : ∀ v ∈ Set.Ioi (0:ℝ), clampG (E.φ A) E.F v = 0 := fun v hv =>
          clampG_zero _ _ _ (nonpos_of_monotone_integrable _ hmo hint v hv)
        intro a ha b hb _
        rw [hz a ha, hz b hb]
      · intro a ha b hb hab
        exact max_le_max le_rfl (min_le_min (han ha hb hab) (Fb_antitone E.F hab))
    have hAa := theorem_A_a E.F (E.K z) E.cycleLaw hdelay hper _ hgm (clampG_bdd _ _) hanti hintc
    exact ⟨fun htop => reduce_to_renewal E z A hA 0 (hAa.1 htop), fun hne => fin (hAa.2 hne)⟩
  · exact ⟨fun htop => absurd htop hμ.ne, fun _ => bv_case E z A hA hper hμ hbv⟩
  · refine ⟨fun htop => absurd htop hμ.ne, fun _ => fin ?_⟩
    have hintc : IntegrableOn (clampG (E.φ A) E.F) (Set.Ioi 0) :=
      Integrable.mono' (Fb_integrableOn E.F E.cycleLaw hμ) hgm.aestronglyMeasurable
        (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs, abs_of_nonneg (clampG_nonneg _ _ _)]; exact clampG_le_Fb _ _ _)
    have hlim : Tendsto (clampG (E.φ A) E.F) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (Fb_tendsto E.F)
        (fun v => clampG_nonneg _ _ v) (fun v => clampG_le_Fb _ _ v)
    exact theorem_1 E.F (E.K z) E.cycleLaw hdelay _ hgm (clampG_bdd _ _) hintc hlim hS hμ
