-- Prove2me | solution 1 for PalmQueueing.Ordering.s_order_mean
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:29:50.221921+00:00
-- url     : https://prove2.me/submissions/4b39dacf-b29e-4cc8-8170-d19e030792b7

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders
import Definitions.Def_PalmQueueing_Ordering_TimeStationary

/-!
# Lemma 4.4.2: the `S`-order compares mean cycle lengths (§4.4, p.302)
-/


namespace PalmQueueing.Ordering

open MeasureTheory Filter Topology

/-- the test function `(t - a)⁺` lies in `I-i`. -/
lemma phi_mem_classIL {n : ℕ} (a : ℝ) (ha : 0 < a) :
    (fun z : Fin (n + 1) → ℝ => max (z 0 - a) 0) ∈ classIL (classI (n + 1)) := by
  refine ⟨fun z => (Set.Ioi a).indicator (fun _ => (1 : ℝ)) (z 0), ?_, ?_, ?_⟩
  · intro x y hxy
    have h0 := hxy 0
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (lt_of_lt_of_le h1 h0) h2
    · norm_num
    · exact le_rfl
  · intro x
    simp only [Fin.cons_zero]
    exact (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioi
  · intro z
    simp only [Fin.cons_zero]
    set t := z 0 with ht
    rcases le_or_gt 0 t with h0 | h0
    · rw [intervalIntegral.integral_of_le h0, integral_indicator measurableSet_Ioi,
        setIntegral_const, measureReal_restrict_apply measurableSet_Ioi]
      have : Set.Ioi a ∩ Set.Ioc 0 t = Set.Ioc a t := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, lt_trans ha h1, h2⟩
      rw [this, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal', smul_eq_mul, mul_one]
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h0.le,
        integral_indicator measurableSet_Ioi, setIntegral_const,
        measureReal_restrict_apply measurableSet_Ioi]
      have : Set.Ioi a ∩ Set.Ioc t 0 = ∅ := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2; linarith
      rw [this, measureReal_empty, zero_smul, neg_zero]
      rw [max_eq_right (by linarith)]

lemma phi_integrable {n : ℕ} (a : ℝ) (ha : 0 < a) (F0 : Measure (Fin (n + 1) → ℝ))
    (hint : Integrable (fun z : Fin (n + 1) → ℝ => z 0) F0) :
    Integrable (fun z : Fin (n + 1) → ℝ => max (z 0 - a) 0) F0 := by
  refine hint.mono ?_ ?_
  · have hmeas : Measurable fun z : Fin (n + 1) → ℝ => z 0 := measurable_pi_apply 0
    exact ((hmeas.sub_const a).max measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    simp only [Real.norm_eq_abs]
    rcases le_or_gt (z 0 - a) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h.le, abs_of_pos h]
      linarith [le_abs_self (z 0)]

lemma mean_pos {n : ℕ} (F0 : Measure (Fin (n + 1) → ℝ)) (hdom : SOrderDomain F0) :
    0 < ∫ z, z 0 ∂F0 := by
  obtain ⟨hprob, hnull, hint⟩ := hdom
  have hae : ∀ᵐ z ∂F0, 0 < z 0 := by
    rw [ae_iff]; simpa using hnull
  rw [integral_pos_iff_support_of_nonneg_ae (hae.mono fun z hz => hz.le) hint]
  have h1 : F0 {z : Fin (n + 1) → ℝ | 0 < z 0} = 1 := by
    rw [← prob_compl_eq_zero_iff (measurableSet_lt measurable_const (measurable_pi_apply 0))]
    have : {z : Fin (n + 1) → ℝ | 0 < z 0}ᶜ = {z | z 0 ≤ 0} := by ext z; simp
    rw [this]; exact hnull
  have h2 : {z : Fin (n + 1) → ℝ | 0 < z 0} ⊆ Function.support (fun z : Fin (n + 1) → ℝ => z 0) :=
    fun z hz => ne_of_gt hz
  calc (0 : ENNReal) < 1 := by norm_num
    _ = F0 {z : Fin (n + 1) → ℝ | 0 < z 0} := h1.symm
    _ ≤ _ := measure_mono h2

lemma min_integral_eq {n : ℕ} (a : ℝ) (ha : 0 < a) (F0 : Measure (Fin (n + 1) → ℝ))
    (hint : Integrable (fun z : Fin (n + 1) → ℝ => z 0) F0) :
    ∫ z, min (z 0) a ∂F0 = (∫ z, z 0 ∂F0) - ∫ z, max (z 0 - a) 0 ∂F0 := by
  rw [← integral_sub hint (phi_integrable a ha F0 hint)]
  congr 1; ext z
  rcases le_total (z 0) a with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

lemma min_div_integral {n : ℕ} (a : ℝ) (ha : 0 < a) (F0 : Measure (Fin (n + 1) → ℝ)) :
    (∫ z, min (z 0) a ∂F0) / a = ∫ z, min (z 0 / a) 1 ∂F0 := by
  rw [← integral_div]
  congr 1; ext z
  rw [← min_div_div_right ha.le, div_self ha.ne']

/-- dominated convergence: `∫ min (z 0 / a_k) 1 → 1` as `a_k = 1/(k+1) → 0`. -/
lemma tendsto_min_div {n : ℕ} (F0 : Measure (Fin (n + 1) → ℝ)) (hdom : SOrderDomain F0) :
    Tendsto (fun k : ℕ => ∫ z, min (z 0 / (1 / ((k : ℝ) + 1))) 1 ∂F0) atTop (𝓝 1) := by
  obtain ⟨hprob, hnull, hint⟩ := hdom
  have hae : ∀ᵐ z ∂F0, 0 < z 0 := by
    rw [ae_iff]; simpa using hnull
  have hmeas : Measurable fun z : Fin (n + 1) → ℝ => z 0 := measurable_pi_apply 0
  have key := tendsto_integral_of_dominated_convergence
    (F := fun (k : ℕ) (z : Fin (n + 1) → ℝ) => min (z 0 / (1 / ((k : ℝ) + 1))) 1)
    (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) ?_ (integrable_const (μ := F0) (1 : ℝ)) ?_ ?_
  · simpa using key
  · intro k
    exact ((hmeas.div_const _).min measurable_const).aestronglyMeasurable
  · intro k
    refine hae.mono fun z hz => ?_
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have : 0 ≤ min (z 0 / (1 / ((k : ℝ) + 1))) 1 := le_min (by positivity) zero_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg this]
    exact min_le_right _ _
  · refine hae.mono fun z hz => ?_
    apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / z 0)
    refine ⟨N, fun k hk => ?_⟩
    symm
    apply min_eq_right
    rw [div_div_eq_mul_div, div_one]
    have : 1 / z 0 ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [div_le_iff₀ hz] at this
    nlinarith

theorem s_order_mean_core {n : ℕ} (F0 F0' : Measure (Fin (n + 1) → ℝ))
    (hdom : SOrderDomain F0) (hdom' : SOrderDomain F0')
    (hle : SILe F0 F0') :
    (∫ z, z 0 ∂F0) ≤ ∫ z, z 0 ∂F0' := by
  set m := ∫ z, z 0 ∂F0 with hm
  set m' := ∫ z, z 0 ∂F0' with hm'
  have hmpos : 0 < m := mean_pos F0 hdom
  have hm'pos : 0 < m' := mean_pos F0' hdom'
  -- the key inequality for each a > 0
  have key : ∀ a : ℝ, 0 < a →
      (∫ z, min (z 0 / a) 1 ∂F0') / m' ≤ (∫ z, min (z 0 / a) 1 ∂F0) / m := by
    intro a ha
    have h := hle _ (phi_mem_classIL a ha) (phi_integrable a ha F0 hdom.2.2)
      (phi_integrable a ha F0' hdom'.2.2)
    rw [← min_div_integral a ha, ← min_div_integral a ha, min_integral_eq a ha F0 hdom.2.2,
      min_integral_eq a ha F0' hdom'.2.2]
    rw [← hm, ← hm'] at *
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_div_iff₀ hmpos hm'pos] at h
    nlinarith
  have hlim : (1 : ℝ) / m' ≤ 1 / m := by
    refine le_of_tendsto_of_tendsto' ((tendsto_min_div F0' hdom').div_const m')
      ((tendsto_min_div F0 hdom).div_const m) fun k => key _ (by positivity)
  exact (one_div_le_one_div hm'pos hmpos).mp hlim

end PalmQueueing.Ordering

open PalmQueueing.Ordering
open MeasureTheory

theorem solution {n : ℕ} (F0 F0' : Measure (Fin (n + 1) → ℝ))
    (hdom : SOrderDomain F0) (hdom' : SOrderDomain F0')
    (hle : SILe F0 F0') :
    (∫ z, z 0 ∂F0) ≤ ∫ z, z 0 ∂F0' := by
  exact s_order_mean_core F0 F0' hdom hdom' hle
