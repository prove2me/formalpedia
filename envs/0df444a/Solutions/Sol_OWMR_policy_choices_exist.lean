-- Prove2me | solution 1 for OWMR.policy_choices_exist
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:39:03.86565+00:00
-- url     : https://prove2.me/submissions/f0223f4f-7cf7-4f4c-8961-3f0d21b32c3e

import Theorems.Thm_OWMR_single_location_lemma
import Theorems.Thm_OWMR_F_properties
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_renewal_concave_dfr
import Definitions.Def_owmr_fifo_policy
import Definitions.Def_owmr_consolidation_policy
import Definitions.Def_owmr_dfr_policy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Order.Interval.Set.Infinite

/-!
The choices required by Definition 1 (`IsFIFOChoice`), Definition 2 (`IsConChoice`) and
Definition D.1 (`IsDFRChoice`) exist for every network with at least one retailer under the
standing assumptions (for Definition D.1, together with the DFR demand assumption of
Theorem D.1). Canonical optimal pairs come from Lemma 1 (`single_location_lemma`); minimizing
half windows, targets and mirror centers exist because the corresponding window averages are
continuous (and coercive where the search is unbounded); the shortened DFR window exists by the
intermediate value theorem, since the renewal function is concave under DFR demand.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace ChoiceEx

/-! ### Newsvendor costs `y ↦ 𝔼[H (y - X)⁺ + p (X - y)⁺]` -/

private noncomputable def nvCost {β : Type} [MeasurableSpace β] (P : Measure β) (X : β → ℝ)
    (H p y : ℝ) : ℝ :=
  ∫ b, (H * max (y - X b) 0 + p * max (X b - y) 0) ∂P

section nv

variable {β : Type} [MeasurableSpace β] (P : Measure β) [IsProbabilityMeasure P] (X : β → ℝ)

private lemma nv_integrable (hX : Integrable X P) (H p y : ℝ) :
    Integrable (fun b => H * max (y - X b) 0 + p * max (X b - y) 0) P :=
  (((integrable_const y).sub hX).pos_part.const_mul _).add
    ((hX.sub (integrable_const y)).pos_part.const_mul _)

omit [IsProbabilityMeasure P] in
private lemma nv_nonneg (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) : 0 ≤ nvCost P X H p y :=
  integral_nonneg fun b =>
    add_nonneg (mul_nonneg hH (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

private lemma nv_lower (hX : Integrable X P) (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    H * (y - ∫ b, X b ∂P) ≤ nvCost P X H p y ∧ p * (∫ b, X b ∂P - y) ≤ nvCost P X H p y := by
  have hi := nv_integrable P X hX H p y
  constructor
  · have e : H * (y - ∫ b, X b ∂P) = ∫ b, H * (y - X b) ∂P := by
      rw [integral_const_mul, integral_sub (integrable_const y) hX, integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((((integrable_const y).sub hX)).const_mul H) hi fun b => ?_
    have h1 : H * (y - X b) ≤ H * max (y - X b) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hH
    have h2 : 0 ≤ p * max (X b - y) 0 := mul_nonneg hp (le_max_right _ _)
    simp only
    linarith
  · have e : p * (∫ b, X b ∂P - y) = ∫ b, p * (X b - y) ∂P := by
      rw [integral_const_mul, integral_sub hX (integrable_const y), integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((hX.sub (integrable_const y)).const_mul p) hi fun b => ?_
    have h1 : p * (X b - y) ≤ p * max (X b - y) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hp
    have h2 : 0 ≤ H * max (y - X b) 0 := mul_nonneg hH (le_max_right _ _)
    simp only
    linarith

private lemma nv_lip (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (y y' : ℝ) :
    |nvCost P X H p y - nvCost P X H p y'| ≤ (H + p) * |y - y'| := by
  unfold nvCost
  rw [← integral_sub (nv_integrable P X hX H p y) (nv_integrable P X hX H p y')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ b, |H * max (y - X b) 0 + p * max (X b - y) 0
          - (H * max (y' - X b) 0 + p * max (X b - y') 0)| ∂P
      ≤ ∫ _b, (H + p) * |y - y'| ∂P := by
        refine integral_mono ((nv_integrable P X hX H p y).sub
          (nv_integrable P X hX H p y')).abs (integrable_const _) fun b => ?_
        have k1 := abs_max_sub_max_le_abs (y - X b) (y' - X b) 0
        have k2 := abs_max_sub_max_le_abs (X b - y) (X b - y') 0
        rw [show y - X b - (y' - X b) = y - y' by ring] at k1
        rw [show X b - y - (X b - y') = -(y - y') by ring, abs_neg] at k2
        calc |H * max (y - X b) 0 + p * max (X b - y) 0
              - (H * max (y' - X b) 0 + p * max (X b - y') 0)|
            = |H * (max (y - X b) 0 - max (y' - X b) 0)
                + p * (max (X b - y) 0 - max (X b - y') 0)| := by ring_nf
          _ ≤ |H * (max (y - X b) 0 - max (y' - X b) 0)|
                + |p * (max (X b - y) 0 - max (X b - y') 0)| := abs_add_le _ _
          _ = H * |max (y - X b) 0 - max (y' - X b) 0|
                + p * |max (X b - y) 0 - max (X b - y') 0| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg hp]
          _ ≤ H * |y - y'| + p * |y - y'| :=
              add_le_add (mul_le_mul_of_nonneg_left k1 hH) (mul_le_mul_of_nonneg_left k2 hp)
          _ = (H + p) * |y - y'| := by ring
    _ = (H + p) * |y - y'| := by simp [integral_const, probReal_univ]

private lemma nv_continuous (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    Continuous (nvCost P X H p) := by
  have hL : LipschitzWith (Real.toNNReal (H + p)) (nvCost P X H p) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    exact nv_lip P X hX H p hH hp y y'
  exact hL.continuous

private lemma nv_convex (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    ConvexOn ℝ Set.univ (nvCost P X H p) := by
  refine ⟨convex_univ, fun y _ y' _ a c ha hc hac => ?_⟩
  simp only [smul_eq_mul]
  unfold nvCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((nv_integrable P X hX H p y).const_mul a)
      ((nv_integrable P X hX H p y').const_mul c)]
  refine integral_mono (nv_integrable P X hX H p _)
    (((nv_integrable P X hX H p y).const_mul a).add ((nv_integrable P X hX H p y').const_mul c))
    fun b => ?_
  have hs : a * X b + c * X b = X b := by rw [← add_mul, hac, one_mul]
  have k1 : max (a * y + c * y' - X b) 0 ≤ a * max (y - X b) 0 + c * max (y' - X b) 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hc (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (y - X b) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (y' - X b) 0) hc
    linarith
  have k2 : max (X b - (a * y + c * y')) 0 ≤ a * max (X b - y) 0 + c * max (X b - y') 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hc (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (X b - y) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (X b - y') 0) hc
    linarith
  have := mul_le_mul_of_nonneg_left k1 hH
  have := mul_le_mul_of_nonneg_left k2 hp
  simp only
  linarith

private lemma nv_anti (hX : Integrable X P) (hX0 : ∀ b, 0 ≤ X b) (H p : ℝ) (hp : 0 ≤ p) :
    AntitoneOn (nvCost P X H p) (Set.Iic 0) := by
  intro y hy y' hy' hyy'
  simp only [Set.mem_Iic] at hy hy'
  unfold nvCost
  refine integral_mono (nv_integrable P X hX H p y') (nv_integrable P X hX H p y) fun b => ?_
  have e1 : max (y - X b) 0 = 0 := max_eq_right (by linarith [hX0 b])
  have e2 : max (y' - X b) 0 = 0 := max_eq_right (by linarith [hX0 b])
  have e3 : max (X b - y) 0 = X b - y := max_eq_left (by linarith [hX0 b])
  have e4 : max (X b - y') 0 = X b - y' := max_eq_left (by linarith [hX0 b])
  simp only [e1, e2, e3, e4]
  nlinarith

private lemma nv_coercive (hX : Integrable X P) (H p : ℝ) (hH : 0 < H) (hp : 0 < p) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ nvCost P X H p y := by
  intro C
  set c := ∫ b, X b ∂P
  set m := min H p with hm
  have hm0 : 0 < m := lt_min hH hp
  refine ⟨|c| + max C 0 / m, fun y hy => ?_⟩
  have hlow := nv_lower P X hX H p y hH.le hp.le
  have hyc : max C 0 / m ≤ |y - c| := by
    have := abs_sub_abs_le_abs_sub y c
    linarith
  have hmc : max C 0 ≤ m * |y - c| := by
    rw [div_le_iff₀ hm0] at hyc
    linarith
  have hkey : m * |y - c| ≤ nvCost P X H p y := by
    rcases le_or_gt c y with h | h
    · rw [abs_of_nonneg (by linarith)]
      calc m * (y - c) ≤ H * (y - c) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
        _ ≤ _ := hlow.1
    · rw [abs_of_neg (by linarith)]
      calc m * -(y - c) = m * (c - y) := by ring
        _ ≤ p * (c - y) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ ≤ _ := hlow.2
  linarith [le_max_left C 0]

end nv

/-! ### Integrability of lead-time demands -/

private lemma integrable_marginal {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

private lemma integrable_aggregate {n : ℕ} (N : Network n) (hN : N.Standing) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) N.aggregate := by
  unfold Network.aggregate
  have hm : Measurable fun x : DemandVec n => ∑ i, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hm.aemeasurable]
  have h : Integrable (fun x : DemandVec n => ∑ i, ((x i : ℝ≥0) : ℝ)) N.μ :=
    integrable_finsetSum _ fun i _ => by
      have h1 := integrable_toReal_of_lintegral_ne_top
        (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
        ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
      simpa using h1
  simpa [Function.comp_def, NNReal.coe_sum] using h

private lemma integrable_psum (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ)) (Measure.pi fun _ : Fin L => ρ) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => ρ) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 hρ

/-! ### Renewal windows -/

lemma renewalM_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) :
    renewalM ρ w = renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalM renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Ico]
  refine tsum_congr fun k => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
  constructor
  · intro h; exact ⟨Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _, h⟩
  · exact fun h => h.2

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma intOn_Ico (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w : ℝ) :
    IntegrableOn F (Set.Ico 0 w) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := w)).exists_bound_of_continuousOn
    hF.continuousOn
  exact Measure.integrableOn_of_bounded (renewalMeasure_Ico_lt_top ρ hρ w).ne
    hF.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ico fun x hx =>
      hC x (Set.Ico_subset_Icc_self hx))

lemma int_ge_const (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w c : ℝ) (h : ∀ x ∈ Set.Ico 0 w, c ≤ F x) :
    c * (renewalMeasure ρ (Set.Ico 0 w)).toReal
      ≤ ∫ x in Set.Ico 0 w, F x ∂(renewalMeasure ρ) := by
  have h1 := setIntegral_mono_on
    (integrableOn_const (C := c) (renewalMeasure_Ico_lt_top ρ hρ w).ne)
    (intOn_Ico ρ hρ F hF w) measurableSet_Ico h
  rwa [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm] at h1

lemma one_le_renewal_toReal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) {w : ℝ} (hw : 0 < w) :
    1 ≤ (renewalMeasure ρ (Set.Ico 0 w)).toReal := by
  have := ENNReal.toReal_mono (renewalMeasure_Ico_lt_top ρ hρ w).ne (one_le_renewal ρ w hw)
  simpa using this


/-! ### Minimizers and window averages -/

/-- A continuous coercive function on `ℝ` attains its minimum. -/
lemma exists_min_coercive (g : ℝ → ℝ) (hg : Continuous g)
    (hco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ g y) : ∃ x, ∀ y, g x ≤ g y := by
  obtain ⟨R, hR⟩ := hco (g 0)
  obtain ⟨x, -, hxmin⟩ := (isCompact_Icc (a := -|R|) (b := |R|)).exists_isMinOn
    ⟨0, by simp [abs_nonneg]⟩ hg.continuousOn
  refine ⟨x, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (-|R|) |R|
  · exact hxmin hy
  · have h1 : R ≤ |y| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith [abs_nonneg R])]
        linarith [le_abs_self R]
      · rw [abs_of_pos (by linarith [abs_nonneg R])]
        linarith [le_abs_self R]
    have h0 : g x ≤ g 0 := hxmin ⟨by simp [abs_nonneg], by simp [abs_nonneg]⟩
    exact h0.trans (hR y h1)

lemma bdd_Icc (f : ℝ → ℝ) (hfc : Continuous f) (s S : ℝ) : ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := S)).exists_bound_of_continuousOn
    hfc.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

/-- Window integrals of a continuous function depend continuously on the window position. -/
lemma window_cont (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (f : ℝ → ℝ) (hf : Continuous f) (w : ℝ) :
    Continuous fun t => ∫ x in Set.Ico 0 w, f (t - x) ∂(renewalMeasure ρ) := by
  haveI : IsFiniteMeasure ((renewalMeasure ρ).restrict (Set.Ico 0 w)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact renewalMeasure_Ico_lt_top ρ hρ w⟩
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t₀ - 1 - w) (b := t₀ + 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · exact Filter.Eventually.of_forall fun t =>
      (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    refine ae_restrict_of_forall_mem measurableSet_Ico fun x hx => ?_
    exact hC (t - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · exact ae_of_all _ fun x => (hf.comp (continuous_id.sub continuous_const)).continuousAt

/-- Renewal-reward for the `(s,S)` policy without setup cost. -/
lemma ss_window (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ y, 0 ≤ f y) (s S : ℝ) (hsS : s < S) :
    ssAvgCost ρ f 0 s S = ENNReal.ofReal ((∫ x in Set.Ico 0 (S - s), f (S - x) ∂(renewalMeasure ρ))
      / (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal) := by
  rw [ss_renewal_reward ρ hρ f hfc.measurable hf0 0 s S le_rfl hsS (bdd_Icc f hfc s S), zero_add]

/-- A half window with the smallest average holding and backlog cost exists. -/
lemma best_half_window_exists (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (sh Sh : ℝ) (hsS : sh < Sh) : ∃ s S : ℝ, IsBestHalfWindow ρ f sh Sh s S := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = (Sh - sh) / 2 := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hGc := window_cont ρ hρ f hfc w
  have hc : Continuous fun s' : ℝ => ∫ x in Set.Ico 0 w, f (s' + w - x) ∂(renewalMeasure ρ) :=
    hGc.comp (continuous_id.add continuous_const)
  obtain ⟨s0, hs0, hmin⟩ := (isCompact_Icc (a := sh) (b := Sh - w)).exists_isMinOn
    ⟨sh, le_rfl, by linarith⟩ hc.continuousOn
  have hN : 0 < (renewalMeasure ρ (Set.Ico 0 w)).toReal :=
    lt_of_lt_of_le one_pos (one_le_renewal_toReal ρ hρ hw0)
  refine ⟨s0, s0 + w, hs0.1, by linarith, by linarith [hs0.2], by rw [← hwdef]; ring,
    fun s' S' h1 h2 h3 h4 => ?_⟩
  rw [← hwdef] at h4
  have hS' : S' = s' + w := by linarith
  rw [ss_window ρ hρ f hfc hf0 s0 (s0 + w) (by linarith), ss_window ρ hρ f hfc hf0 s' S' h2,
    show s0 + w - s0 = w by ring, h4, hS']
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hN.le)
  exact hmin (show s' ∈ Set.Icc sh (Sh - w) from ⟨h1, by linarith⟩)

/-- For a fixed width, a target with the smallest average holding and backlog cost exists. -/
lemma best_target_exists (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (w : ℝ) (hw : 0 < w) :
    ∃ S : ℝ, ∀ S' : ℝ, ssAvgCost ρ f 0 (S - w) S ≤ ssAvgCost ρ f 0 (S' - w) S' := by
  have hGc := window_cont ρ hρ f hfc w
  have hN1 : 1 ≤ (renewalMeasure ρ (Set.Ico 0 w)).toReal := one_le_renewal_toReal ρ hρ hw
  have hGco : ∀ C : ℝ, ∃ R : ℝ, ∀ t, R ≤ |t| →
      C ≤ ∫ x in Set.Ico 0 w, f (t - x) ∂(renewalMeasure ρ) := by
    intro C
    obtain ⟨R, hR⟩ := hfco (max C 0)
    refine ⟨|R| + w, fun t ht => ?_⟩
    have hge : max C 0 * (renewalMeasure ρ (Set.Ico 0 w)).toReal
        ≤ ∫ x in Set.Ico 0 w, f (t - x) ∂(renewalMeasure ρ) :=
      int_ge_const ρ hρ (fun x => f (t - x)) (hfc.comp (continuous_const.sub continuous_id)) w
        (max C 0) (fun x hx => hR (t - x) (by
          have h1 := abs_sub_abs_le_abs_sub t x
          rw [abs_of_nonneg hx.1] at h1
          linarith [le_abs_self R, hx.2]))
    have : max C 0 ≤ max C 0 * (renewalMeasure ρ (Set.Ico 0 w)).toReal :=
      le_mul_of_one_le_right (le_max_right _ _) hN1
    linarith [le_max_left C 0]
  obtain ⟨S, hS⟩ := exists_min_coercive _ hGc hGco
  refine ⟨S, fun S' => ?_⟩
  rw [ss_window ρ hρ f hfc hf0 (S - w) S (by linarith),
    ss_window ρ hρ f hfc hf0 (S' - w) S' (by linarith), sub_sub_cancel, sub_sub_cancel]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hS S') (by linarith))

/-! ### Mirror centers -/

lemma whLoss_nonneg' (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : 0 ≤ whLoss h p y :=
  add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

lemma whLoss_ge (h p y : ℝ) (hh : 0 < h) (hp : 0 < p) : min h p * |y| ≤ whLoss h p y := by
  unfold whLoss
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, max_eq_left hy, max_eq_right (by linarith)]
    have := min_le_left h p
    nlinarith
  · rw [abs_of_nonpos hy, max_eq_right hy, max_eq_left (by linarith)]
    have := min_le_right h p
    nlinarith

lemma whLoss_cont (h p : ℝ) : Continuous (whLoss h p) := by
  unfold whLoss
  fun_prop

lemma mirror_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    mirrorAvg ρ h p s S a = ssAvgCost ρ (fun y => whLoss h p (a - y)) 0 s S := by
  unfold mirrorAvg ssAvgCost ssPeriodCost
  simp only [zero_mul, zero_add]

/-- Every `(s,S)` policy with `s < S` has a mirror center. -/
lemma mirror_center_exists (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (h p : ℝ) (hh : 0 < h) (hp : 0 < p) (s S : ℝ) (hsS : s < S) :
    ∃ a : ℝ, mirrorAvg ρ h p s S a = mirrorCost ρ h p s S := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = S - s := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hwdef]; linarith
  have hN1 : 1 ≤ (renewalMeasure ρ (Set.Ico 0 w)).toReal := one_le_renewal_toReal ρ hρ hw
  have hψc : Continuous fun z : ℝ => whLoss h p (-z) := (whLoss_cont h p).comp continuous_neg
  have hGc := window_cont ρ hρ (fun z : ℝ => whLoss h p (-z)) hψc w
  have hmA : ∀ a, mirrorAvg ρ h p s S a = ENNReal.ofReal
      ((∫ x in Set.Ico 0 w, whLoss h p (-(S - a - x)) ∂(renewalMeasure ρ))
        / (renewalMeasure ρ (Set.Ico 0 w)).toReal) := by
    intro a
    rw [mirror_eq, ss_window ρ hρ (fun y => whLoss h p (a - y))
      ((whLoss_cont h p).comp (continuous_const.sub continuous_id))
      (fun y => whLoss_nonneg' h p _ hh.le hp.le) s S hsS, ← hwdef]
    congr 2
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    congr 1
    ring
  have hmc : Continuous fun a : ℝ =>
      ∫ x in Set.Ico 0 w, whLoss h p (-(S - a - x)) ∂(renewalMeasure ρ) :=
    hGc.comp (continuous_const.sub continuous_id)
  have hmco : ∀ C : ℝ, ∃ R : ℝ, ∀ a, R ≤ |a| →
      C ≤ ∫ x in Set.Ico 0 w, whLoss h p (-(S - a - x)) ∂(renewalMeasure ρ) := by
    intro C
    have hc : 0 < min h p := lt_min hh hp
    refine ⟨|S| + w + max C 0 / min h p, fun a ha => ?_⟩
    have hge : max C 0 * (renewalMeasure ρ (Set.Ico 0 w)).toReal
        ≤ ∫ x in Set.Ico 0 w, whLoss h p (-(S - a - x)) ∂(renewalMeasure ρ) := by
      refine int_ge_const ρ hρ (fun x => whLoss h p (-(S - a - x)))
        (hψc.comp (continuous_const.sub continuous_id)) w (max C 0) (fun x hx => ?_)
      refine le_trans ?_ (whLoss_ge h p _ hh hp)
      have h1 : |a| - |S| - w ≤ |-(S - a - x)| := by
        rw [show -(S - a - x) = a - (S - x) by ring]
        have h2 := abs_sub_abs_le_abs_sub a (S - x)
        have h3 : |S - x| ≤ |S| + w := by
          have := abs_sub S x
          rw [abs_of_nonneg hx.1] at this
          linarith [hx.2]
        linarith
      have h4 : max C 0 / min h p ≤ |-(S - a - x)| := by linarith
      calc max C 0 = min h p * (max C 0 / min h p) := by field_simp
        _ ≤ min h p * |-(S - a - x)| := mul_le_mul_of_nonneg_left h4 hc.le
    have : max C 0 ≤ max C 0 * (renewalMeasure ρ (Set.Ico 0 w)).toReal :=
      le_mul_of_one_le_right (le_max_right _ _) hN1
    linarith [le_max_left C 0]
  obtain ⟨a0, ha0⟩ := exists_min_coercive _ hmc hmco
  refine ⟨a0, le_antisymm ?_ (by unfold mirrorCost; exact iInf_le _ a0)⟩
  unfold mirrorCost
  refine le_iInf fun a => ?_
  rw [hmA a0, hmA a]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (ha0 a) (by linarith))

/-! ### The network's single-location data -/

variable {n : ℕ}

lemma marg_pos (N : Network n) (hN : N.Standing) (i : Fin n) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂(N.marginal i) := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_pos i

lemma marg_fin (N : Network n) (hN : N.Standing) (i : Fin n) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(N.marginal i) < ∞ := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_lt_top i

lemma agg_lintegral (N : Network n) :
    ∫⁻ x, (x : ℝ≥0∞) ∂N.aggregate = ∑ i, ∫⁻ x, ((x i : ℝ≥0) : ℝ≥0∞) ∂N.μ := by
  have hmsum : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  unfold Network.aggregate
  rw [lintegral_map measurable_coe_nnreal_ennreal hmsum]
  have e : ∀ x : DemandVec n, ((∑ i, x i : ℝ≥0) : ℝ≥0∞) = ∑ i, ((x i : ℝ≥0) : ℝ≥0∞) :=
    fun x => by push_cast; rfl
  simp_rw [e]
  rw [lintegral_finsetSum _ fun i _ => (measurable_pi_apply i).coe_nnreal_ennreal]

lemma agg_pos (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂N.aggregate := by
  rw [agg_lintegral]
  exact lt_of_lt_of_le (hN.mean_pos ⟨0, hn⟩)
    (Finset.single_le_sum (f := fun i => ∫⁻ x, ((x i : ℝ≥0) : ℝ≥0∞) ∂N.μ)
      (fun i _ => zero_le) (Finset.mem_univ _))

lemma agg_fin (N : Network n) (hN : N.Standing) : ∫⁻ x, (x : ℝ≥0∞) ∂N.aggregate < ∞ := by
  rw [agg_lintegral]
  exact ENNReal.sum_lt_top.2 fun i _ => hN.mean_lt_top i

lemma F_int (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) :=
  integrable_psum _ (integrable_marginal N hN i) _

lemma F_coercive (N : Network n) (hN : N.Standing) (i : Fin n) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ N.F i y :=
  nv_coercive (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
    (fun z => ∑ j, (z j : ℝ)) (F_int N hN i) (N.H i) N.p (hN.H_pos i) hN.p_pos

lemma F_cont (N : Network n) (hN : N.Standing) (i : Fin n) : Continuous (N.F i) :=
  nv_continuous (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
    (fun z => ∑ j, (z j : ℝ)) (F_int N hN i) (N.H i) N.p (hN.H_pos i).le hN.p_pos.le

lemma F_lipschitz (N : Network n) (hN : N.Standing) (i : Fin n) :
    ∃ L : ℝ≥0, LipschitzWith L (N.F i) := by
  refine ⟨Real.toNNReal (N.H i + N.p), LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [hN.H_pos i, hN.p_pos])]
  exact (F_properties N hN i).2.2.1 y y'

lemma fL0_eq_nv (N : Network n) : N.fL0 = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate)
    (fun z => ∑ j, (z j : ℝ)) N.h N.p := by
  funext y
  unfold Network.fL0 nvCost whLoss
  congr 1
  funext z
  rw [neg_sub]

lemma fL0_int (N : Network n) (hN : N.Standing) :
    Integrable (fun z : Fin N.L0 → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin N.L0 => N.aggregate) :=
  integrable_psum _ (integrable_aggregate N hN) _

lemma fL0_props (N : Network n) (hN : N.Standing) :
    (∀ y, 0 ≤ N.fL0 y) ∧ ConvexOn ℝ Set.univ N.fL0 ∧
      (∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ N.fL0 y) ∧ Continuous N.fL0 ∧
      (∃ L : ℝ≥0, LipschitzWith L N.fL0) ∧ AntitoneOn N.fL0 (Set.Iic 0) := by
  rw [fL0_eq_nv]
  have hX0 : ∀ z : Fin N.L0 → ℝ≥0, 0 ≤ ∑ j, (z j : ℝ) := fun z =>
    Finset.sum_nonneg fun j _ => (z j).2
  refine ⟨fun y => nv_nonneg _ _ _ _ _ hN.h_pos.le hN.p_pos.le,
    nv_convex _ _ (fL0_int N hN) _ _ hN.h_pos.le hN.p_pos.le,
    nv_coercive _ _ (fL0_int N hN) _ _ hN.h_pos hN.p_pos,
    nv_continuous _ _ (fL0_int N hN) _ _ hN.h_pos.le hN.p_pos.le, ?_,
    nv_anti _ _ (fL0_int N hN) hX0 _ _ hN.p_pos.le⟩
  refine ⟨Real.toNNReal (N.h + N.p), LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [hN.h_pos, hN.p_pos])]
  exact nv_lip _ _ (fL0_int N hN) _ _ hN.h_pos.le hN.p_pos.le y y'

lemma Kmax_nonneg (hn : 0 < n) (N : Network n) (hN : N.Standing) : 0 ≤ N.Kmax := by
  unfold Network.Kmax
  exact le_trans (hN.K_nonneg ⟨0, hn⟩)
    (le_ciSup (f := fun i => N.K i) (Set.finite_range _).bddAbove (⟨0, hn⟩ : Fin n))

/-! ### Lemma 1 for the retailer and supplier problems -/

lemma retailer_canonical (N : Network n) (hN : N.Standing) (i : Fin n) (k : ℝ) (hk : 0 < k) :
    ∃ sh Sh : ℝ, IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh := by
  obtain ⟨J, -, -, -, -, hpos, -, -, -⟩ := single_location_lemma (N.marginal i) (marg_pos N hN i)
    (marg_fin N hN i) (N.F i) (F_properties N hN i).1 (F_properties N hN i).2.1
    (F_coercive N hN i) (F_lipschitz N hN i) k hk.le
  obtain ⟨sh, Sh, hcan, -, -⟩ := hpos hk
  exact ⟨sh, Sh, hcan⟩

lemma retailer_J_zero (N : Network n) (hN : N.Standing) (i : Fin n) :
    N.J i 0 = ENNReal.ofReal (⨅ y, N.F i y) := by
  obtain ⟨J, -, hval, -, -, -, hzero, -, -⟩ := single_location_lemma (N.marginal i)
    (marg_pos N hN i) (marg_fin N hN i) (N.F i) (F_properties N hN i).1
    (F_properties N hN i).2.1 (F_coercive N hN i) (F_lipschitz N hN i) 0 le_rfl
  obtain ⟨x, hx, hJx, -⟩ := hzero rfl
  have hinf : (⨅ y, N.F i y) = N.F i x :=
    le_antisymm (ciInf_le ⟨N.F i x, by rintro _ ⟨y, rfl⟩; exact hx y⟩ x) (le_ciInf hx)
  unfold Network.J
  rw [hval, hJx, hinf]

lemma supplier_canonical (hn : 0 < n) (N : Network n) (hN : N.Standing) (k : ℝ) (hk : 0 < k) :
    ∃ sh Sh : ℝ, IsCanonicalOptimum N.aggregate N.fL0 k sh Sh := by
  obtain ⟨h0, hcv, hco, -, hL, -⟩ := fL0_props N hN
  obtain ⟨J, -, -, -, -, hpos, -, -, -⟩ := single_location_lemma N.aggregate (agg_pos hn N hN)
    (agg_fin N hN) N.fL0 h0 hcv hco hL k hk.le
  obtain ⟨sh, Sh, hcan, -, -⟩ := hpos hk
  exact ⟨sh, Sh, hcan⟩

/-- Rule (iii) of Definition 1: a supplier `(s₀, S₀)` policy attaining `J₀(K₀ + K_max)`. -/
lemma supplier_pair (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    ∃ s0 S0 : ℝ, s0 ≤ S0 ∧
      ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) s0 S0 = N.J0 (N.K0 + N.Kmax) := by
  obtain ⟨h0, hcv, hco, -, hL, -⟩ := fL0_props N hN
  have hk : 0 ≤ N.K0 + N.Kmax := add_nonneg hN.K0_nonneg (Kmax_nonneg hn N hN)
  obtain ⟨J, -, -, -, -, hpos, hzero, -, -⟩ := single_location_lemma N.aggregate
    (agg_pos hn N hN) (agg_fin N hN) N.fL0 h0 hcv hco hL _ hk
  rcases hk.lt_or_eq with h | h
  · obtain ⟨s, S, ⟨hsS, hcost, -⟩, -, -⟩ := hpos h
    exact ⟨s, S, hsS.le, hcost⟩
  · obtain ⟨x, -, -, hx⟩ := hzero h.symm
    exact ⟨x, x, le_rfl, hx⟩

/-- A nonnegative minimizer of `f_{L₀}` (for Definition 2 with `K₀ = 0`). -/
lemma supplier_nonneg_min (N : Network n) (hN : N.Standing) :
    ∃ x, 0 ≤ x ∧ ∀ y, N.fL0 x ≤ N.fL0 y := by
  obtain ⟨-, -, hco, hc, -, hanti⟩ := fL0_props N hN
  obtain ⟨x, hx⟩ := exists_min_coercive N.fL0 hc hco
  refine ⟨max x 0, le_max_right _ _, fun y => ?_⟩
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
    exact hx y
  · rw [max_eq_right h]
    exact (hanti (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h).trans (hx y)

/-! ### The shortened DFR window -/

/-- Under DFR demand the renewal function `x ↦ U[0,x]` is concave on `[0, ∞)`. -/
lemma dfr_concave (N : Network n) (hN : N.Standing) (i : Fin n) (hD : N.DFRPositive i) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (renewalMeasure (N.marginal i) (Set.Icc 0 x)).toReal) := by
  have hρ := marg_pos N hN i
  obtain ⟨-, hdfr⟩ := hD
  have hS0 : 0 < N.survival i 0 := by
    unfold Network.survival
    by_contra hneg
    have h0 : N.marginal i {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)} = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm (not_lt.1 hneg) ENNReal.toReal_nonneg)
        with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    have hae : (fun x : ℝ≥0 => (x : ℝ≥0∞)) =ᵐ[N.marginal i] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun x hx => ?_) h0
      simp only [Set.mem_setOf_eq, Pi.zero_apply, ENNReal.coe_eq_zero] at hx ⊢
      exact lt_of_le_of_ne x.2 (Ne.symm (by exact_mod_cast hx))
    have : ∫⁻ x, (x : ℝ≥0∞) ∂(N.marginal i) = 0 := by rw [lintegral_congr_ae hae]; simp
    rw [this] at hρ
    exact lt_irrefl _ hρ
  have hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      (N.marginal i {z : ℝ≥0 | η * x + (1 - η) * y < (z : ℝ)}).toReal
        ≤ (N.marginal i {z : ℝ≥0 | x < (z : ℝ)}).toReal ^ η
          * (N.marginal i {z : ℝ≥0 | y < (z : ℝ)}).toReal ^ (1 - η) := by
    intro x y η hx hy hη0 hη1
    have h := hdfr x y η hx hy hη0 hη1
    unfold Network.survival at h hS0
    set S0 := (N.marginal i {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)}).toReal
    rw [Real.div_rpow ENNReal.toReal_nonneg hS0.le, Real.div_rpow ENNReal.toReal_nonneg hS0.le,
      div_mul_div_comm, ← Real.rpow_add hS0, show η + (1 - η) = 1 by ring, Real.rpow_one,
      div_le_div_iff_of_pos_right hS0] at h
    exact h
  exact renewal_concave_dfr (N.marginal i) hρ hlc

/-- Intermediate values of the renewal function: with `U[0,x]` concave, every level strictly
between `U{0}` and `U[0, ŵ)` is `U[0, w)` for some `0 < w ≤ ŵ`. -/
lemma window_ivt (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (renewalMeasure ρ (Set.Icc 0 x)).toReal))
    (wh v : ℝ) (hwh : 0 < wh) (hv0 : (renewalMeasure ρ {0}).toReal < v)
    (hv1 : v < (renewalMeasure ρ (Set.Ico 0 wh)).toReal) :
    ∃ w, 0 < w ∧ w ≤ wh ∧ (renewalMeasure ρ (Set.Ico 0 w)).toReal = v := by
  have hfinIco : ∀ x, renewalMeasure ρ (Set.Ico 0 x) ≠ ∞ := fun x =>
    (renewalMeasure_Ico_lt_top ρ hρ x).ne
  have hfinIcc : ∀ x, renewalMeasure ρ (Set.Icc 0 x) ≠ ∞ := fun x =>
    ne_top_of_le_ne_top (hfinIco (x + 1)) (measure_mono (Set.Icc_subset_Ico_right (by linarith)))
  have hWc : ContinuousOn (fun x : ℝ => (renewalMeasure ρ (Set.Icc 0 x)).toReal) (Set.Ioi 0) := by
    have h := hconc.continuousOn_interior
    rwa [interior_Ici] at h
  -- `U[0,x) = U[0,x]` for `x > 0`
  have hφW : ∀ x : ℝ, 0 < x →
      (renewalMeasure ρ (Set.Ico 0 x)).toReal = (renewalMeasure ρ (Set.Icc 0 x)).toReal := by
    intro x hx
    apply le_antisymm
    · exact ENNReal.toReal_mono (hfinIcc x) (measure_mono Set.Ico_subset_Icc_self)
    · have hcont : ContinuousAt (fun x : ℝ => (renewalMeasure ρ (Set.Icc 0 x)).toReal) x :=
        hWc.continuousAt (Ioi_mem_nhds hx)
      have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio x))
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact ENNReal.toReal_mono (hfinIco x) (measure_mono (Set.Icc_subset_Ico_right hy))
  have hφc : ContinuousOn (fun x : ℝ => (renewalMeasure ρ (Set.Ico 0 x)).toReal) (Set.Ioi 0) :=
    hWc.congr fun x hx => hφW x hx
  -- a short window below the level `v`
  have hanti : Antitone fun k : ℕ => Set.Icc (0 : ℝ) (1 / ((k : ℝ) + 1)) := by
    intro k k' hkk'
    refine Set.Icc_subset_Icc_right ?_
    have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hinter : (⋂ k : ℕ, Set.Icc (0 : ℝ) (1 / ((k : ℝ) + 1))) = {0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · intro h
      refine le_antisymm ?_ (h 0).1
      by_contra hx
      push_neg at hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx
      linarith [(h k).2]
    · rintro rfl k
      exact ⟨le_rfl, by positivity⟩
  have hlim : Tendsto (fun k : ℕ => renewalMeasure ρ (Set.Icc 0 (1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (renewalMeasure ρ {0})) := by
    have h := tendsto_measure_iInter_atTop (μ := renewalMeasure ρ)
      (s := fun k : ℕ => Set.Icc (0 : ℝ) (1 / ((k : ℝ) + 1)))
      (fun k => measurableSet_Icc.nullMeasurableSet) hanti ⟨0, hfinIcc _⟩
    rw [hinter] at h
    exact h
  have hfin0 : renewalMeasure ρ {0} ≠ ∞ :=
    ne_top_of_le_ne_top (hfinIco 1) (measure_mono (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨le_rfl, one_pos⟩))
  have hlt : renewalMeasure ρ {0} < ENNReal.ofReal v :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin0).2 hv0
  have hsmall : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨k, hk1, hk2⟩ := ((hlim.eventually (gt_mem_nhds hlt)).and
    (hsmall.eventually (Iio_mem_nhds hwh))).exists
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hεwh : ε < wh := hk2
  have hφε : (renewalMeasure ρ (Set.Ico 0 ε)).toReal < v :=
    lt_of_le_of_lt (ENNReal.toReal_mono (hfinIcc ε) (measure_mono Set.Ico_subset_Icc_self))
      (ENNReal.toReal_lt_of_lt_ofReal hk1)
  obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc hεwh.le
    (hφc.mono fun x hx => lt_of_lt_of_le hε0 hx.1) ⟨hφε.le, hv1.le⟩
  exact ⟨w, lt_of_lt_of_le hε0 hw.1, hw.2, hwv⟩

/-! ### The choices -/

lemma dfrT_le_one (N : Network n) (i : Fin n) (sh Sh : ℝ) : N.dfrT i sh Sh ≤ 1 := by
  unfold Network.dfrT
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma conG_gt_one (m : ℝ) (hm : 0 < m) : 1 < conG m := by
  unfold conG conGammaBar
  have : 0 < 32 / (57 * m) := by positivity
  linarith

lemma conZeta_pos (m : ℝ) (hm : 0 < m) : 0 < conZeta m := by
  unfold conZeta
  have h := conG_gt_one m hm
  exact div_pos (by linarith) (by linarith)

lemma conB_ge_one (m : ℝ) (hm : 0 < m) : 1 ≤ conB m := by
  unfold conB conG conGammaBar
  have : 0 < 32 / (57 * m) := by positivity
  linarith

lemma rat_enum_nonempty : Nonempty (ℕ ≃ {q : ℚ // 0 < q ∧ q < 1}) := by
  haveI : Infinite {q : ℚ // 0 < q ∧ q < 1} := Set.Ioo.infinite (by norm_num : (0 : ℚ) < 1)
  haveI : Encodable {q : ℚ // 0 < q ∧ q < 1} := Encodable.ofCountable _
  letI := Denumerable.ofEncodableOfInfinite {q : ℚ // 0 < q ∧ q < 1}
  exact ⟨(Denumerable.eqv _).symm⟩

/-- Definition 1. -/
lemma fifo_exists (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    ∃ c : FIFOChoice n, IsFIFOChoice N c := by
  have hret : ∀ i, ∃ t : ℝ × ℝ × ℝ,
      (0 < N.K i → ∃ sh Sh s' S' : ℝ,
        IsCanonicalOptimum (N.marginal i) (N.F i) (5 * N.K i / 3) sh Sh ∧
        IsBestHalfWindow (N.marginal i) (N.F i) sh Sh s' S' ∧
        ((t.1 = sh ∧ t.2.1 = Sh ∧ N.augCost i sh Sh ≤ N.augCost i s' S') ∨
          (t.1 = s' ∧ t.2.1 = S' ∧ N.augCost i s' S' ≤ N.augCost i sh Sh)) ∧
        mirrorAvg (N.marginal i) N.h N.p t.1 t.2.1 t.2.2
          = mirrorCost (N.marginal i) N.h N.p t.1 t.2.1) ∧
      (N.K i = 0 → t.1 = t.2.1 ∧ (∀ y, N.F i t.2.1 ≤ N.F i y) ∧ t.2.2 = t.2.1) := by
    intro i
    rcases (hN.K_nonneg i).lt_or_eq with hK | hK
    · obtain ⟨sh, Sh, hcan⟩ := retailer_canonical N hN i (5 * N.K i / 3) (by positivity)
      obtain ⟨s', S', hbw⟩ := best_half_window_exists (N.marginal i) (marg_pos N hN i) (N.F i)
        (F_cont N hN i) (F_properties N hN i).1 sh Sh hcan.1
      rcases le_total (N.augCost i sh Sh) (N.augCost i s' S') with hle | hle
      · obtain ⟨a, ha⟩ := mirror_center_exists (N.marginal i) (marg_pos N hN i) N.h N.p hN.h_pos
          hN.p_pos sh Sh hcan.1
        exact ⟨(sh, Sh, a), fun _ => ⟨sh, Sh, s', S', hcan, hbw, Or.inl ⟨rfl, rfl, hle⟩, ha⟩,
          fun h => absurd h hK.ne'⟩
      · obtain ⟨a, ha⟩ := mirror_center_exists (N.marginal i) (marg_pos N hN i) N.h N.p hN.h_pos
          hN.p_pos s' S' hbw.2.1
        exact ⟨(s', S', a), fun _ => ⟨sh, Sh, s', S', hcan, hbw, Or.inr ⟨rfl, rfl, hle⟩, ha⟩,
          fun h => absurd h hK.ne'⟩
    · obtain ⟨x, hx⟩ := exists_min_coercive (N.F i) (F_cont N hN i) (F_coercive N hN i)
      exact ⟨(x, x, x), fun h => absurd h (by rw [← hK]; exact lt_irrefl 0),
        fun _ => ⟨rfl, hx, rfl⟩⟩
  choose t ht using hret
  obtain ⟨s0, S0, hsS0, hcost0⟩ := supplier_pair hn N hN
  exact ⟨⟨fun i => (t i).1, fun i => (t i).2.1, fun i => (t i).2.2, s0, S0⟩,
    fun i hK => (ht i).1 hK, fun i hK => (ht i).2 hK, hsS0, hcost0⟩

/-- Definition 2. -/
lemma con_exists (hn : 0 < n) (N : Network n) (hN : N.Standing) (m : ℝ) (hm : 0 < m) :
    ∃ c : ConChoice n, IsConChoice N m c := by
  have hret : ∀ i, ∃ t : Bool × ℝ × ℝ,
      (ENNReal.ofReal ((⨅ y, N.F i y) + N.K i)
          ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i) →
        t.1 = false ∧ t.2.1 = t.2.2 ∧ ∀ y, N.F i t.2.2 ≤ N.F i y) ∧
      (ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)
          < ENNReal.ofReal ((⨅ y, N.F i y) + N.K i) →
        t.1 = true ∧ ∃ sh Sh : ℝ,
          IsCanonicalOptimum (N.marginal i) (N.F i) (conZeta m * N.K i) sh Sh ∧
          (ENNReal.ofReal (conZeta m * N.K i)
                / (N.J i (conZeta m * N.K i) * renewalM (N.marginal i) (Sh - sh))
              ≤ ENNReal.ofReal (conU m) →
            IsBestHalfWindow (N.marginal i) (N.F i) sh Sh t.2.1 t.2.2) ∧
          (ENNReal.ofReal (conU m)
              < ENNReal.ofReal (conZeta m * N.K i)
                / (N.J i (conZeta m * N.K i) * renewalM (N.marginal i) (Sh - sh)) →
            t.2.1 = sh ∧ t.2.2 = Sh)) := by
    intro i
    obtain ⟨x, hx⟩ := exists_min_coercive (N.F i) (F_cont N hN i) (F_coercive N hN i)
    by_cases h1 : ENNReal.ofReal ((⨅ y, N.F i y) + N.K i)
        ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)
    · exact ⟨(false, x, x), fun _ => ⟨rfl, rfl, hx⟩, fun h2 => absurd h2 (not_lt.2 h1)⟩
    · have hK : 0 < N.K i := by
        rcases (hN.K_nonneg i).lt_or_eq with hK | hK
        · exact hK
        · exfalso
          apply h1
          have hB := conB_ge_one m hm
          rw [← hK, mul_zero, add_zero, retailer_J_zero N hN i,
            ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          have hinf0 : 0 ≤ ⨅ y, N.F i y := le_ciInf fun y => (F_properties N hN i).1 y
          nlinarith
      have hk : 0 < conZeta m * N.K i := mul_pos (conZeta_pos m hm) hK
      obtain ⟨sh, Sh, hcan⟩ := retailer_canonical N hN i _ hk
      by_cases hu : ENNReal.ofReal (conZeta m * N.K i)
          / (N.J i (conZeta m * N.K i) * renewalM (N.marginal i) (Sh - sh))
          ≤ ENNReal.ofReal (conU m)
      · obtain ⟨s', S', hbw⟩ := best_half_window_exists (N.marginal i) (marg_pos N hN i) (N.F i)
          (F_cont N hN i) (F_properties N hN i).1 sh Sh hcan.1
        exact ⟨(true, s', S'), fun h => absurd h h1,
          fun _ => ⟨rfl, sh, Sh, hcan, fun _ => hbw, fun h => absurd h (not_lt.2 hu)⟩⟩
      · exact ⟨(true, sh, Sh), fun h => absurd h h1,
          fun _ => ⟨rfl, sh, Sh, hcan, fun h => absurd h hu, fun _ => ⟨rfl, rfl⟩⟩⟩
  choose t ht using hret
  obtain ⟨q, hq⟩ : ∃ q : ℝ × ℝ,
      (0 < N.K0 → ∃ sh Sh : ℝ, IsCanonicalOptimum N.aggregate N.fL0 (conG m * N.K0) sh Sh ∧
        q.1 = sh + max (-sh) 0 ∧ q.2 = Sh + max (-sh) 0) ∧
      (N.K0 = 0 → q.1 = q.2 ∧ 0 ≤ q.2 ∧ ∀ y, N.fL0 q.2 ≤ N.fL0 y) := by
    rcases hN.K0_nonneg.lt_or_eq with hK0 | hK0
    · obtain ⟨sh, Sh, hcan⟩ := supplier_canonical hn N hN (conG m * N.K0)
        (mul_pos (by linarith [conG_gt_one m hm]) hK0)
      exact ⟨(sh + max (-sh) 0, Sh + max (-sh) 0), fun _ => ⟨sh, Sh, hcan, rfl, rfl⟩,
        fun h => absurd h hK0.ne'⟩
    · obtain ⟨x, hx0, hx⟩ := supplier_nonneg_min N hN
      exact ⟨(x, x), fun h => absurd h (by rw [← hK0]; exact lt_irrefl 0),
        fun _ => ⟨rfl, hx0, hx⟩⟩
  obtain ⟨e⟩ := rat_enum_nonempty
  exact ⟨⟨fun i => (t i).2.1, fun i => (t i).2.2, fun i => (t i).1, q.1, q.2, ⟨0, hn⟩,
      fun _ => 1 / 2, e⟩,
    fun i => ⟨(ht i).1, (ht i).2⟩, hq.1, hq.2, fun _ => ⟨by norm_num, by norm_num⟩⟩

/-- Definition D.1. -/
lemma dfr_exists (hn : 0 < n) (N : Network n) (hN : N.Standing) (θ : ℝ) (hθ : 0 < θ)
    (hD : ∀ i, 0 < N.K i → N.DFRPositive i) : ∃ c : FIFOChoice n, IsDFRChoice N θ c := by
  have hret : ∀ i, ∃ t : ℝ × ℝ × ℝ,
      (N.K i = 0 → t.1 = t.2.1 ∧ (∀ y, N.F i t.2.1 ≤ N.F i y) ∧ t.2.2 = t.2.1) ∧
      (0 < N.K i → ∃ sh Sh : ℝ,
        IsCanonicalOptimum (N.marginal i) (N.F i) (N.K i / θ) sh Sh ∧
        (N.dfrT i sh Sh = 1 → t.1 = sh ∧ t.2.1 = Sh ∧
          mirrorAvg (N.marginal i) N.h N.p sh Sh t.2.2
            = mirrorCost (N.marginal i) N.h N.p sh Sh) ∧
        (N.dfrT i sh Sh < 1 → N.dfrT i sh Sh ≤ N.dfrT0 i sh Sh →
          t.1 = t.2.1 ∧ (∀ y, N.F i t.2.1 ≤ N.F i y) ∧ t.2.2 = t.2.1) ∧
        (N.dfrT i sh Sh < 1 → N.dfrT0 i sh Sh < N.dfrT i sh Sh →
          renewalM (N.marginal i) (t.2.1 - t.1)
              = ENNReal.ofReal (N.dfrT i sh Sh) * renewalM (N.marginal i) (Sh - sh) ∧
          (∀ S' : ℝ, ssAvgCost (N.marginal i) (N.F i) 0 t.1 t.2.1
            ≤ ssAvgCost (N.marginal i) (N.F i) 0 (S' - (t.2.1 - t.1)) S') ∧
          mirrorAvg (N.marginal i) N.h N.p t.1 t.2.1 t.2.2
            = mirrorCost (N.marginal i) N.h N.p t.1 t.2.1)) := by
    intro i
    obtain ⟨x, hx⟩ := exists_min_coercive (N.F i) (F_cont N hN i) (F_coercive N hN i)
    rcases (hN.K_nonneg i).lt_or_eq with hK | hK
    swap
    · exact ⟨(x, x, x), fun _ => ⟨rfl, hx, rfl⟩,
        fun h => absurd h (by rw [← hK]; exact lt_irrefl 0)⟩
    obtain ⟨sh, Sh, hcan⟩ := retailer_canonical N hN i (N.K i / θ) (div_pos hK hθ)
    have hsS := hcan.1
    rcases (dfrT_le_one N i sh Sh).lt_or_eq with htlt | hteq
    · by_cases hcase : N.dfrT i sh Sh ≤ N.dfrT0 i sh Sh
      · -- base stock at a minimizer
        exact ⟨(x, x, x), fun h => absurd h hK.ne', fun _ => ⟨sh, Sh, hcan,
          fun h => absurd h htlt.ne, fun _ _ => ⟨rfl, hx, rfl⟩,
          fun _ h => absurd h (not_lt.2 hcase)⟩⟩
      · -- the shortened window
        push_neg at hcase
        have hconc := dfr_concave N hN i (hD i hK)
        have hwh0 : 0 < Sh - sh := by linarith
        have hMfin : renewalM (N.marginal i) (Sh - sh) ≠ ⊤ := by
          rw [renewalM_eq]
          exact (renewalMeasure_Ico_lt_top _ (marg_pos N hN i) _).ne
        have hM1 : 1 ≤ (renewalM (N.marginal i) (Sh - sh)).toReal := by
          rw [renewalM_eq]
          exact one_le_renewal_toReal _ (marg_pos N hN i) hwh0
        have ht0nn : 0 ≤ N.dfrT0 i sh Sh :=
          div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        have hv0 : (renewalMeasure (N.marginal i) {0}).toReal
            < N.dfrT i sh Sh * (renewalM (N.marginal i) (Sh - sh)).toReal := by
          have h := hcase
          unfold Network.dfrT0 at h
          rwa [div_lt_iff₀ (by linarith)] at h
        have hv1 : N.dfrT i sh Sh * (renewalM (N.marginal i) (Sh - sh)).toReal
            < (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal := by
          rw [← renewalM_eq]
          nlinarith
        obtain ⟨w, hw0, -, hwv⟩ := window_ivt (N.marginal i) (marg_pos N hN i) hconc (Sh - sh) _
          hwh0 hv0 hv1
        obtain ⟨S, hS⟩ := best_target_exists (N.marginal i) (marg_pos N hN i) (N.F i)
          (F_cont N hN i) (F_properties N hN i).1 (F_coercive N hN i) w hw0
        obtain ⟨a, ha⟩ := mirror_center_exists (N.marginal i) (marg_pos N hN i) N.h N.p hN.h_pos
          hN.p_pos (S - w) S (by linarith)
        refine ⟨(S - w, S, a), fun h => absurd h hK.ne', fun _ => ⟨sh, Sh, hcan,
          fun h => absurd h htlt.ne, fun _ h => absurd h (not_le.2 hcase),
          fun _ _ => ⟨?_, ?_, ha⟩⟩⟩
        · show renewalM (N.marginal i) (S - (S - w))
            = ENNReal.ofReal (N.dfrT i sh Sh) * renewalM (N.marginal i) (Sh - sh)
          rw [sub_sub_cancel, renewalM_eq,
            ← ENNReal.ofReal_toReal (renewalMeasure_Ico_lt_top _ (marg_pos N hN i) w).ne, hwv,
            ENNReal.ofReal_mul (le_trans ht0nn hcase.le), ENNReal.ofReal_toReal hMfin]
        · intro S'
          show ssAvgCost (N.marginal i) (N.F i) 0 (S - w) S
            ≤ ssAvgCost (N.marginal i) (N.F i) 0 (S' - (S - (S - w))) S'
          rw [sub_sub_cancel]
          exact hS S'
    · -- `t = 1`: the canonical pair
      obtain ⟨a, ha⟩ := mirror_center_exists (N.marginal i) (marg_pos N hN i) N.h N.p hN.h_pos
        hN.p_pos sh Sh hsS
      exact ⟨(sh, Sh, a), fun h => absurd h hK.ne', fun _ => ⟨sh, Sh, hcan,
        fun _ => ⟨rfl, rfl, ha⟩, fun h => absurd h (by rw [hteq]; exact lt_irrefl 1),
        fun h => absurd h (by rw [hteq]; exact lt_irrefl 1)⟩⟩
  choose t ht using hret
  obtain ⟨s0, S0, hsS0, hcost0⟩ := supplier_pair hn N hN
  exact ⟨⟨fun i => (t i).1, fun i => (t i).2.1, fun i => (t i).2.2, s0, S0⟩,
    fun i hK => (ht i).1 hK, fun i hK => (ht i).2 hK, hsS0, hcost0⟩

end ChoiceEx

open ChoiceEx in
theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    (∃ c : FIFOChoice n, IsFIFOChoice N c) ∧
    (∀ m : ℝ, 0 < m → ∃ c : ConChoice n, IsConChoice N m c) ∧
    (∀ θ : ℝ, 0 < θ → (∀ i, 0 < N.K i → N.DFRPositive i) →
      ∃ c : FIFOChoice n, IsDFRChoice N θ c) :=
  ⟨fifo_exists hn N hN, fun m hm => con_exists hn N hN m hm,
    fun θ hθ hD => dfr_exists hn N hN θ hθ hD⟩
