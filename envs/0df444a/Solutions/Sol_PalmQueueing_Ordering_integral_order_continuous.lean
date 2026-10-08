-- Prove2me | solution 1 for PalmQueueing.Ordering.integral_order_continuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:34:26.140281+00:00
-- url     : https://prove2.me/submissions/54a50626-73c5-4b8f-bd00-b220a0be943d

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

/-!
# Lemma 4.2.1: the strong order is tested by continuous functions alone (§4.2.2, p.275)
-/


namespace PalmQueueing.Ordering

open MeasureTheory Filter Topology

lemma fin1_eq (x : Fin 1 → ℝ) : x = fun _ => x 0 := by
  funext i; rw [Subsingleton.elim i 0]

lemma coordLe_iff (x y : Fin 1 → ℝ) : CoordLe x y ↔ x 0 ≤ y 0 := by
  constructor
  · intro h; exact h 0
  · intro h i; rw [Subsingleton.elim i 0]; exact h

/-- The continuous criterion, as a hypothesis. -/
def ContCrit (F G : Measure (Fin 1 → ℝ)) : Prop :=
  ∀ f : (Fin 1 → ℝ) → ℝ,
    Continuous f → (∀ x, 0 ≤ f x) → (∀ x y : Fin 1 → ℝ, CoordLe x y → f x ≤ f y) →
    Integrable f F → Integrable f G →
    (∫ x, f x ∂F) ≤ ∫ x, f x ∂G

lemma measure_le_of_approx (F G : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F]
    [IsProbabilityMeasure G] (hcont : ContCrit F G)
    (U : Set (Fin 1 → ℝ)) (hU : MeasurableSet U) (g : ℕ → (Fin 1 → ℝ) → ℝ)
    (hgc : ∀ k, Continuous (g k)) (hg0 : ∀ k x, 0 ≤ g k x) (hg1 : ∀ k x, g k x ≤ 1)
    (hgm : ∀ k x y, CoordLe x y → g k x ≤ g k y)
    (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (U.indicator 1 x))) : F U ≤ G U := by
  have hint : ∀ (μ : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure μ] (k : ℕ),
      Integrable (g k) μ := by
    intro μ _ k
    refine (integrable_const (1 : ℝ)).mono' (hgc k).measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 k x)]; exact hg1 k x
  have hlimF : ∀ (μ : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure μ],
      Tendsto (fun k => ∫ x, g k x ∂μ) atTop (𝓝 (μ.real U)) := by
    intro μ _
    rw [← integral_indicator_one hU]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun k => (hgc k).measurable.aestronglyMeasurable) (integrable_const 1) ?_
      (Filter.Eventually.of_forall hlim)
    intro k
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 k x)]; exact hg1 k x
  have hle : F.real U ≤ G.real U :=
    le_of_tendsto_of_tendsto' (hlimF F) (hlimF G) fun k =>
      hcont (g k) (hgc k) (hg0 k) (hgm k) (hint F k) (hint G k)
  rw [measureReal_def, measureReal_def] at hle
  exact (ENNReal.toReal_le_toReal (measure_ne_top F U) (measure_ne_top G U)).mp hle

lemma measure_Ioi_le (F G : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F]
    [IsProbabilityMeasure G] (hcont : ContCrit F G) (a : ℝ) :
    F {x | a < x 0} ≤ G {x | a < x 0} := by
  have hmeas : Measurable fun x : Fin 1 → ℝ => x 0 := measurable_pi_apply 0
  refine measure_le_of_approx F G hcont _ (measurableSet_lt measurable_const hmeas)
    (fun k x => min 1 (max 0 (((k : ℝ) + 1) * (x 0 - a)))) ?_ ?_ ?_ ?_ ?_
  · intro k
    exact continuous_const.min (continuous_const.max
      (continuous_const.mul ((continuous_apply 0).sub continuous_const)))
  · intro k x; exact le_min zero_le_one (le_max_left _ _)
  · intro k x; exact min_le_left _ _
  · intro k x y hxy
    have := (coordLe_iff x y).1 hxy
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro x
    rcases lt_or_ge a (x 0) with h | h
    · have hx : x ∈ {x : Fin 1 → ℝ | a < x 0} := h
      rw [Set.indicator_of_mem hx, Pi.one_apply]
      apply tendsto_const_nhds.congr'
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x 0 - a))
      refine ⟨N, fun k hk => ?_⟩
      have hpos : 0 < x 0 - a := by linarith
      have : 1 ≤ ((k : ℝ) + 1) * (x 0 - a) := by
        rw [div_lt_iff₀ hpos] at hN
        have : (N : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      symm
      rw [max_eq_right (by linarith), min_eq_left this]
    · have hx : x ∉ {x : Fin 1 → ℝ | a < x 0} := not_lt.mpr h
      rw [Set.indicator_of_notMem hx]
      have : ∀ k : ℕ, min 1 (max 0 (((k : ℝ) + 1) * (x 0 - a))) = 0 := by
        intro k
        have : ((k : ℝ) + 1) * (x 0 - a) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        rw [max_eq_left this, min_eq_right zero_le_one]
      simp only [this]
      exact tendsto_const_nhds

lemma measure_Ici_le (F G : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F]
    [IsProbabilityMeasure G] (hcont : ContCrit F G) (a : ℝ) :
    F {x | a ≤ x 0} ≤ G {x | a ≤ x 0} := by
  have hmeas : Measurable fun x : Fin 1 → ℝ => x 0 := measurable_pi_apply 0
  refine measure_le_of_approx F G hcont _ (measurableSet_le measurable_const hmeas)
    (fun k x => min 1 (max 0 (1 + ((k : ℝ) + 1) * (x 0 - a)))) ?_ ?_ ?_ ?_ ?_
  · intro k
    exact continuous_const.min (continuous_const.max
      (continuous_const.add (continuous_const.mul ((continuous_apply 0).sub continuous_const))))
  · intro k x; exact le_min zero_le_one (le_max_left _ _)
  · intro k x; exact min_le_left _ _
  · intro k x y hxy
    have := (coordLe_iff x y).1 hxy
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro x
    rcases le_or_gt a (x 0) with h | h
    · have hx : x ∈ {x : Fin 1 → ℝ | a ≤ x 0} := h
      rw [Set.indicator_of_mem hx, Pi.one_apply]
      have : ∀ k : ℕ, min 1 (max 0 (1 + ((k : ℝ) + 1) * (x 0 - a))) = 1 := by
        intro k
        have : 0 ≤ ((k : ℝ) + 1) * (x 0 - a) := mul_nonneg (by positivity) (by linarith)
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      simp only [this]
      exact tendsto_const_nhds
    · have hx : x ∉ {x : Fin 1 → ℝ | a ≤ x 0} := not_le.mpr h
      rw [Set.indicator_of_notMem hx]
      apply tendsto_const_nhds.congr'
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (a - x 0))
      refine ⟨N, fun k hk => ?_⟩
      have hpos : 0 < a - x 0 := by linarith
      have : 1 + ((k : ℝ) + 1) * (x 0 - a) ≤ 0 := by
        rw [div_lt_iff₀ hpos] at hN
        have : (N : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      symm
      rw [max_eq_left this, min_eq_right zero_le_one]

/-- up-sets have larger `G`-measure -/
lemma upset_measure_le (F G : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F]
    [IsProbabilityMeasure G] (hcont : ContCrit F G)
    (U : Set (Fin 1 → ℝ)) (hup : ∀ x y, x ∈ U → CoordLe x y → y ∈ U) : F U ≤ G U := by
  set U' : Set ℝ := {r | (fun _ => r) ∈ U} with hU'
  have hUeq : U = {x | x 0 ∈ U'} := by
    ext x
    simp only [hU', Set.mem_setOf_eq]
    constructor
    · intro h; rw [← fin1_eq x]; exact h
    · intro h; rw [fin1_eq x]; exact h
  have hup' : ∀ r s, r ∈ U' → r ≤ s → s ∈ U' := by
    intro r s hr hrs
    exact hup _ _ hr ((coordLe_iff _ _).2 hrs)
  rcases Set.eq_empty_or_nonempty U' with hemp | hne
  · have : U = ∅ := by rw [hUeq, hemp]; simp
    rw [this]; simp
  by_cases hbdd : BddBelow U'
  · set a := sInf U' with ha
    have hIoi : ∀ r, a < r → r ∈ U' := by
      intro r hr
      obtain ⟨u, hu, hur⟩ := exists_lt_of_csInf_lt hne hr
      exact hup' u r hu hur.le
    have hIci : ∀ r, r ∈ U' → a ≤ r := fun r hr => csInf_le hbdd hr
    by_cases haU : a ∈ U'
    · have : U = {x | a ≤ x 0} := by
        rw [hUeq]; ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · exact hIci _
        · intro h; rcases h.lt_or_eq with h | h
          · exact hIoi _ h
          · rw [← h]; exact haU
      rw [this]; exact measure_Ici_le F G hcont a
    · have : U = {x | a < x 0} := by
        rw [hUeq]; ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h; rcases (hIci _ h).lt_or_eq with h' | h'
          · exact h'
          · rw [← h'] at h; exact absurd h haU
        · exact hIoi _
      rw [this]; exact measure_Ioi_le F G hcont a
  · have : U = Set.univ := by
      rw [hUeq]; ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [not_bddBelow_iff] at hbdd
      obtain ⟨u, hu, hux⟩ := hbdd (x 0)
      exact hup' u _ hu hux.le
    rw [this]; simp

/-- down-sets have larger `F`-measure -/
lemma downset_measure_le (F G : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F]
    [IsProbabilityMeasure G] (hcont : ContCrit F G)
    (D : Set (Fin 1 → ℝ)) (hD : MeasurableSet D)
    (hdown : ∀ x y, y ∈ D → CoordLe x y → x ∈ D) : G D ≤ F D := by
  have hup : ∀ x y, x ∈ Dᶜ → CoordLe x y → y ∈ Dᶜ := by
    intro x y hx hxy hy
    exact hx (hdown x y hy hxy)
  have h := upset_measure_le F G hcont Dᶜ hup
  rw [prob_compl_eq_one_sub hD, prob_compl_eq_one_sub hD] at h
  have h1 : F D ≤ 1 := prob_le_one
  have h2 : G D ≤ 1 := prob_le_one
  exact (ENNReal.sub_le_sub_iff_left h2 (by norm_num)).mp h

lemma integral_mono_of_monotone (F G : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F]
    [IsProbabilityMeasure G] (hcont : ContCrit F G)
    (f : (Fin 1 → ℝ) → ℝ) (hf : ∀ x y : Fin 1 → ℝ, CoordLe x y → f x ≤ f y)
    (hFi : Integrable f F) (hGi : Integrable f G) :
    (∫ x, f x ∂F) ≤ ∫ x, f x ∂G := by
  have hmeas : Measurable f := by
    have hmono : Monotone fun r : ℝ => f (fun _ => r) := by
      intro r s hrs
      exact hf _ _ ((coordLe_iff _ _).2 hrs)
    have : f = (fun r : ℝ => f (fun _ => r)) ∘ (fun x : Fin 1 → ℝ => x 0) := by
      funext x; simp only [Function.comp]; rw [← fin1_eq x]
    rw [this]
    exact hmono.measurable.comp (measurable_pi_apply 0)
  set fp : (Fin 1 → ℝ) → ℝ := fun x => max (f x) 0 with hfp
  set fm : (Fin 1 → ℝ) → ℝ := fun x => max (-f x) 0 with hfm
  have hfpm : Measurable fp := hmeas.max measurable_const
  have hfmm : Measurable fm := hmeas.neg.max measurable_const
  have hsplit : ∀ x, f x = fp x - fm x := by
    intro x; simp only [hfp, hfm]
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hF : ∫ x, f x ∂F = ∫ x, fp x ∂F - ∫ x, fm x ∂F := by
    rw [← integral_sub hFi.pos_part hFi.neg_part]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hG : ∫ x, f x ∂G = ∫ x, fp x ∂G - ∫ x, fm x ∂G := by
    rw [← integral_sub hGi.pos_part hGi.neg_part]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hfp0 : ∀ μ : Measure (Fin 1 → ℝ), 0 ≤ᵐ[μ] fp := fun μ =>
    Filter.Eventually.of_forall fun x => by show (0 : ℝ) ≤ max (f x) 0; exact le_max_right _ _
  have hfm0 : ∀ μ : Measure (Fin 1 → ℝ), 0 ≤ᵐ[μ] fm := fun μ =>
    Filter.Eventually.of_forall fun x => by show (0 : ℝ) ≤ max (-f x) 0; exact le_max_right _ _
  have hp : ∫ x, fp x ∂F ≤ ∫ x, fp x ∂G := by
    rw [integral_eq_lintegral_of_nonneg_ae (hfp0 F) hfpm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (hfp0 G) hfpm.aestronglyMeasurable]
    have hfin : ∫⁻ x, ENNReal.ofReal (fp x) ∂G ≠ ⊤ := hGi.pos_part.lintegral_lt_top.ne
    apply ENNReal.toReal_mono hfin
    rw [lintegral_eq_lintegral_meas_lt F (hfp0 F) hfpm.aemeasurable,
      lintegral_eq_lintegral_meas_lt G (hfp0 G) hfpm.aemeasurable]
    apply lintegral_mono
    intro t
    apply upset_measure_le F G hcont
    intro x y hx hxy
    simp only [Set.mem_setOf_eq, hfp] at hx ⊢
    exact lt_of_lt_of_le hx (max_le_max (hf x y hxy) le_rfl)
  have hm : ∫ x, fm x ∂G ≤ ∫ x, fm x ∂F := by
    rw [integral_eq_lintegral_of_nonneg_ae (hfm0 G) hfmm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (hfm0 F) hfmm.aestronglyMeasurable]
    have hfin : ∫⁻ x, ENNReal.ofReal (fm x) ∂F ≠ ⊤ := hFi.neg_part.lintegral_lt_top.ne
    apply ENNReal.toReal_mono hfin
    rw [lintegral_eq_lintegral_meas_lt F (hfm0 F) hfmm.aemeasurable,
      lintegral_eq_lintegral_meas_lt G (hfm0 G) hfmm.aemeasurable]
    apply lintegral_mono
    intro t
    apply downset_measure_le F G hcont _ (measurableSet_lt measurable_const hfmm)
    intro x y hy hxy
    simp only [Set.mem_setOf_eq, hfm] at hy ⊢
    exact lt_of_lt_of_le hy (max_le_max (neg_le_neg (hf x y hxy)) le_rfl)
  rw [hF, hG]
  linarith

theorem integral_order_continuous_core (F G : Measure (Fin 1 → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G) :
    StLe F G ↔
      ∀ f : (Fin 1 → ℝ) → ℝ,
        Continuous f → (∀ x, 0 ≤ f x) → (∀ x y : Fin 1 → ℝ, CoordLe x y → f x ≤ f y) →
        Integrable f F → Integrable f G →
        (∫ x, f x ∂F) ≤ ∫ x, f x ∂G := by
  have : IsProbabilityMeasure F := hF
  have : IsProbabilityMeasure G := hG
  constructor
  · intro h f _ _ hmono hFi hGi
    exact h f hmono hFi hGi
  · intro h f hmono hFi hGi
    exact integral_mono_of_monotone F G h f hmono hFi hGi

end PalmQueueing.Ordering

open PalmQueueing.Ordering
open MeasureTheory

theorem solution (F G : Measure (Fin 1 → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G) :
    StLe F G ↔
      ∀ f : (Fin 1 → ℝ) → ℝ,
        Continuous f → (∀ x, 0 ≤ f x) → (∀ x y : Fin 1 → ℝ, CoordLe x y → f x ≤ f y) →
        Integrable f F → Integrable f G →
        (∫ x, f x ∂F) ≤ ∫ x, f x ∂G := by
  exact integral_order_continuous_core F G hF hG
