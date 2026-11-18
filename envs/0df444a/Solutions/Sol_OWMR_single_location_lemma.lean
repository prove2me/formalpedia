-- Prove2me | solution 1 for OWMR.single_location_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:11:44.848402+00:00
-- url     : https://prove2.me/submissions/3eda517c-ce2d-496c-804b-9b63c73c0613

import Theorems.Thm_OWMR_sl_adapted_bound
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_ss_poisson_upper
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.ENNReal
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Lemma 1 (Single-Location Inventory Problem) of the source, for general nonnegative convex,
coercive, Lipschitz `f` and every demand law with positive mean.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace SLL

/-- Splitting off the first demand: `ρ^{⊗(T+1)} ≅ ρ ⊗ ρ^{⊗T}`. -/
private lemma lintegral_pi_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (T : ℕ)
    {F : ℝ≥0 × (Fin T → ℝ≥0) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ y, ∫⁻ z', F (y, z') ∂(Measure.pi fun _ : Fin T => ρ) ∂ρ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => ρ) 0
  have key : ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ z, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => ℝ≥0) 0 z)
          ∂(Measure.pi fun _ : Fin (T + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]

/-! ### The renewal equation for `U` -/

private lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

private lemma lintegral_law_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) = F 0 := by
  rw [lintegral_map hF (measurable_psum 0)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, lintegral_const, measure_univ, mul_one]

private lemma lintegral_law_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin (n + 1) => ρ).map fun z => ∑ j, (z j : ℝ))
      = ∫⁻ y, ∫⁻ x, F ((y : ℝ) + x)
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ := by
  rw [lintegral_map hF (measurable_psum _)]
  have hG : Measurable fun q : ℝ≥0 × (Fin n → ℝ≥0) => F ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)) :=
    hF.comp (measurable_fst.coe_nnreal_real.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_snd).coe_nnreal_real))
  have key : ∫⁻ z, F (∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (n + 1) => ρ)
      = ∫⁻ z, F (((z 0 : ℝ≥0) : ℝ) + ∑ j, ((Fin.tail z j : ℝ≥0) : ℝ))
          ∂(Measure.pi fun _ : Fin (n + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [Fin.sum_univ_succ, Fin.tail]
  rw [key, lintegral_pi_succ ρ n hG]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map (f := fun x => F ((y : ℝ) + x)) (hF.comp (measurable_const_add _))
    (measurable_psum n)]

/-- `U = δ₀ + ρ * U`. -/
private lemma renewal_decomp (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ u, F u ∂(renewalMeasure ρ)
      = F 0 + ∫⁻ y, ∫⁻ u, F ((y : ℝ) + u) ∂(renewalMeasure ρ) ∂ρ := by
  have hU : ∀ g : ℝ → ℝ≥0∞, ∫⁻ x, g x ∂(renewalMeasure ρ)
      = ∑' n : ℕ, ∫⁻ x, g x ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) :=
    fun g => lintegral_sum_measure g _
  have hmeas : ∀ n : ℕ, Measurable fun y : ℝ≥0 => ∫⁻ x, F ((y : ℝ) + x)
      ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) := fun n =>
    Measurable.lintegral_prod_right' (f := fun q : ℝ≥0 × ℝ => F ((q.1 : ℝ) + q.2))
      (hF.comp (measurable_fst.coe_nnreal_real.add measurable_snd))
  rw [hU F, tsum_eq_zero_add' ENNReal.summable, lintegral_law_zero ρ hF]
  congr 1
  simp_rw [lintegral_law_succ ρ _ hF]
  rw [← lintegral_tsum fun n => (hmeas n).aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [hU (fun x => F ((y : ℝ) + x))]

private lemma renewal_Iio_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    renewalMeasure ρ (Set.Iio 0) = 0 := by
  unfold renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  rw [Measure.map_apply (measurable_psum n) measurableSet_Iio]
  have : (fun z : Fin n → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Iio 0 = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Finset.sum_nonneg fun j _ => (z j).2
  rw [this, measure_empty]

private lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (measurable_psum 0) measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

/-- Renewal equation for `x ↦ ∫_{[0, w-x)} G(x+u) U(du)`, for `0 ≤ x < w`. -/
private lemma renewal_window (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) (x : ℝ) (hx0 : 0 ≤ x) (hxw : x < w) :
    ∫⁻ u in Set.Ico 0 (w - x), G (x + u) ∂(renewalMeasure ρ)
      = G x + ∫⁻ y, ∫⁻ u in Set.Ico 0 (w - (x + y)), G ((x + y) + u) ∂(renewalMeasure ρ) ∂ρ := by
  have hae : ∀ᵐ u ∂(renewalMeasure ρ), 0 ≤ u := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (renewal_Iio_zero ρ)] with u hu
    simpa using hu
  rw [← lintegral_indicator measurableSet_Ico,
    renewal_decomp ρ (F := (Set.Ico 0 (w - x)).indicator fun u => G (x + u))
      ((hG.comp (measurable_const_add x)).indicator measurableSet_Ico),
    Set.indicator_of_mem (Set.mem_Ico.2 ⟨le_rfl, by linarith⟩), add_zero]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [← lintegral_indicator measurableSet_Ico]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with u hu
  have hy := NNReal.coe_nonneg y
  by_cases h : u < w - (x + y)
  · rw [Set.indicator_of_mem (Set.mem_Ico.2 ⟨by linarith, by linarith⟩),
      Set.indicator_of_mem (Set.mem_Ico.2 ⟨hu, h⟩), add_assoc]
  · rw [Set.indicator_of_notMem (fun h' => h (by linarith [(Set.mem_Ico.1 h').2])),
      Set.indicator_of_notMem (fun h' => h (Set.mem_Ico.1 h').2)]



/-- If `v → 0`, then `limsup (u + v) ≤ limsup u` in `ℝ≥0∞`. -/
private lemma limsup_add_tendsto_zero (u v : ℕ → ℝ≥0∞) (hv : Tendsto v atTop (𝓝 0)) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ n in atTop, u n + v n ≤ u n + ε :=
    (hv.eventually (ge_mem_nhds hε')).mono fun n hn => add_le_add le_rfl hn
  calc limsup (fun n => u n + v n) atTop ≤ limsup (fun n => u n + (ε : ℝ≥0∞)) atTop :=
        limsup_le_limsup hev
    _ = limsup u atTop + ε :=
        limsup_add_const atTop u _ (by isBoundedDefault) (by isBoundedDefault)

/-! ### The `(s,S)` policy started by one order from position `0` -/

private lemma ssPre_dep (s S : ℝ) : ∀ (t : ℕ) (d d' : ℕ → ℝ≥0), (∀ r < t, d r = d' r) →
    ssPre s S d t = ssPre s S d' t
  | 0, _, _, _ => rfl
  | t + 1, d, d', h => by
    show (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ)
      = (if ssPre s S d' t ≤ s then S else ssPre s S d' t) - (d' t : ℝ)
    rw [ssPre_dep s S t d d' (fun r hr => h r (by omega)), h t (by omega)]

private lemma measurable_ssPre (s S : ℝ) : ∀ t, Measurable fun d : ℕ → ℝ≥0 => ssPre s S d t
  | 0 => measurable_const
  | t + 1 => by
    have ih := measurable_ssPre s S t
    show Measurable fun d : ℕ → ℝ≥0 =>
      (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ)
    exact (Measurable.ite (measurableSet_le ih measurable_const) measurable_const ih).sub
      (measurable_pi_apply t).coe_nnreal_real

/-! ### The `(s,S)` rule started at an arbitrary position -/

/-- Pre-action positions of the `(s,S)` rule started at pre-action position `y0`. -/
def rulePre (y0 s S : ℝ) (d : ℕ → ℝ≥0) : ℕ → ℝ
  | 0 => y0
  | t + 1 => (if rulePre y0 s S d t ≤ s then S else rulePre y0 s S d t) - (d t : ℝ)

/-- The `(s,S)` rule started at pre-action position `y0`, as a single-location policy. -/
def rulePolicy (y0 s S : ℝ) : SLPolicy Unit :=
  fun t _ d => if rulePre y0 s S d t ≤ s then S - rulePre y0 s S d t else 0

lemma rulePre_dep (y0 s S : ℝ) : ∀ (t : ℕ) (d d' : ℕ → ℝ≥0), (∀ r < t, d r = d' r) →
    rulePre y0 s S d t = rulePre y0 s S d' t
  | 0, _, _, _ => rfl
  | t + 1, d, d', h => by
    simp only [rulePre]
    rw [rulePre_dep y0 s S t d d' (fun r hr => h r (by omega)), h t (by omega)]

lemma measurable_rulePre (y0 s S : ℝ) : ∀ t, Measurable fun d : ℕ → ℝ≥0 => rulePre y0 s S d t
  | 0 => measurable_const
  | t + 1 => by
    simp only [rulePre]
    have ih := measurable_rulePre y0 s S t
    exact (Measurable.ite (measurableSet_le ih measurable_const) measurable_const ih).sub
      ((measurable_pi_apply t).coe_nnreal_real)

lemma slPos_rulePolicy (y0 s S : ℝ) (d : ℕ → ℝ≥0) : ∀ t,
    slPos y0 (rulePolicy y0 s S) () d t
      = if rulePre y0 s S d t ≤ s then S else rulePre y0 s S d t
  | 0 => by
    show y0 + ∑ r ∈ Finset.range 1, rulePolicy y0 s S r () d - ∑ r ∈ Finset.range 0, (d r : ℝ)
      = if y0 ≤ s then S else y0
    rw [Finset.sum_range_one, Finset.sum_range_zero, sub_zero]
    show y0 + (if y0 ≤ s then S - y0 else 0) = if y0 ≤ s then S else y0
    split_ifs <;> ring
  | t + 1 => by
    have ih := slPos_rulePolicy y0 s S d t
    have h1 : slPos y0 (rulePolicy y0 s S) () d (t + 1)
        = slPos y0 (rulePolicy y0 s S) () d t + rulePolicy y0 s S (t + 1) () d - (d t : ℝ) := by
      simp only [slPos, Finset.sum_range_succ]
      ring
    have h2 : rulePre y0 s S d (t + 1)
        = (if rulePre y0 s S d t ≤ s then S else rulePre y0 s S d t) - (d t : ℝ) := rfl
    rw [h1, ih]
    simp only [rulePolicy]
    rw [h2]
    split_ifs <;> ring

lemma rulePolicy_cost (f : ℝ → ℝ) (K y0 s S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    slPeriodCost f K y0 (rulePolicy y0 s S) () d t
      = K * (if rulePre y0 s S d t ≤ s ∧ rulePre y0 s S d t < S then 1 else 0)
        + f (if rulePre y0 s S d t ≤ s then S else rulePre y0 s S d t) := by
  unfold slPeriodCost
  rw [slPos_rulePolicy]
  congr 2
  simp only [rulePolicy]
  by_cases h1 : rulePre y0 s S d t ≤ s
  · by_cases h2 : rulePre y0 s S d t < S
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

lemma rulePolicy_adm (y0 s S : ℝ) (hsS : s ≤ S) : SLAdmissible (rulePolicy y0 s S) := by
  refine ⟨fun t u d d' h => ?_, fun t => ?_, fun t u d => ?_⟩
  · simp only [rulePolicy]
    rw [rulePre_dep y0 s S t d d' h]
  · simp only [rulePolicy]
    have hm : Measurable fun ω : Unit × (ℕ → ℝ≥0) => rulePre y0 s S ω.2 t :=
      (measurable_rulePre y0 s S t).comp measurable_snd
    exact Measurable.ite (measurableSet_le hm measurable_const) (measurable_const.sub hm)
      measurable_const
  · simp only [rulePolicy]
    split_ifs with h
    · linarith
    · exact le_rfl

/-- The `(s,S)` rule from any starting position has long-run average cost at most that of the
`(s,S)` policy started at `S`. -/
lemma slAvg_rule_le (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (K y0 s S : ℝ) (hK : 0 ≤ K) (hsS : s ≤ S) :
    slAvgCost ρ f K y0 (rulePolicy y0 s S) (Measure.dirac ()) ≤ ssAvgCost ρ f K s S := by
  obtain ⟨C, hC, hbound⟩ := ss_poisson_upper ρ (fun x : ℝ≥0 => x) measurable_id ρ
    (by simp) hρ f hfc hf0 K s S y0 hK hsS (fun _ _ => True) (fun t d => rulePre y0 s S d t)
    (fun t => by simp) (measurable_rulePre y0 s S) (fun t d d' h => Iff.rfl)
    (rulePre_dep y0 s S) (fun t d _ => trivial) (fun t d _ => rfl) (fun d _ => le_rfl)
    (fun t d h _ => absurd trivial h)
  set A := ssAvgCost ρ f K s S
  have hT : ∀ T : ℕ, 1 ≤ T → (T : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
      (slPeriodCost f K y0 (rulePolicy y0 s S) ω.1 (padHist T ω.2) t)
        ∂((Measure.dirac ()).prod (Measure.pi fun _ : Fin T => ρ)) ≤ A + (T : ℝ≥0∞)⁻¹ * C := by
    intro T hT1
    have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    rw [Measure.dirac_prod]
    have hm : Measurable fun z : Fin T → ℝ≥0 => ∑ t ∈ Finset.range T, ENNReal.ofReal
        (slPeriodCost f K y0 (rulePolicy y0 s S) () (padHist T z) t) := by
      refine Finset.measurable_sum _ fun t _ => ENNReal.measurable_ofReal.comp ?_
      have hp : Measurable fun z : Fin T → ℝ≥0 => padHist T z := by
        refine measurable_pi_lambda _ fun r => ?_
        by_cases h : r < T
        · simp only [padHist, dif_pos h]
          exact measurable_pi_apply _
        · simp only [padHist, dif_neg h]
          exact measurable_const
      have hpre := (measurable_rulePre y0 s S t).comp hp
      simp_rw [rulePolicy_cost]
      exact (measurable_const.mul (Measurable.ite ((measurableSet_le hpre measurable_const).inter
        (measurableSet_lt hpre measurable_const)) measurable_const measurable_const)).add
        (hfc.measurable.comp (Measurable.ite (measurableSet_le hpre measurable_const)
          measurable_const hpre))
    rw [lintegral_map (f := fun ω : Unit × (Fin T → ℝ≥0) => ∑ t ∈ Finset.range T, ENNReal.ofReal
        (slPeriodCost f K y0 (rulePolicy y0 s S) ω.1 (padHist T ω.2) t))
      (hm.comp measurable_snd) measurable_prodMk_left]
    have hb := hbound T T le_rfl
    simp only [if_true] at hb
    calc (T : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal
            (slPeriodCost f K y0 (rulePolicy y0 s S) () (padHist T z) t)
              ∂(Measure.pi fun _ : Fin T => ρ)
        = (T : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal
            (K * (if rulePre y0 s S (padHist T z) t ≤ s ∧ rulePre y0 s S (padHist T z) t < S
              then 1 else 0) + f (if rulePre y0 s S (padHist T z) t ≤ s then S
                else rulePre y0 s S (padHist T z) t)) ∂(Measure.pi fun _ : Fin T => ρ) := by
          simp_rw [rulePolicy_cost]
      _ ≤ (T : ℝ≥0∞)⁻¹ * (T * A + C) := by gcongr
      _ = A + (T : ℝ≥0∞)⁻¹ * C := by
          rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T),
            one_mul]
  have h0 : Tendsto (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * C) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
    simpa using this
  unfold slAvgCost
  calc limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (slPeriodCost f K y0 (rulePolicy y0 s S) ω.1 (padHist T ω.2) t)
            ∂((Measure.dirac ()).prod (Measure.pi fun _ : Fin T => ρ))) atTop
      ≤ limsup (fun T : ℕ => A + (T : ℝ≥0∞)⁻¹ * C) atTop :=
        limsup_le_limsup (eventually_atTop.2 ⟨1, hT⟩)
    _ ≤ limsup (fun _ : ℕ => A) atTop := limsup_add_tendsto_zero _ _ h0
    _ = A := limsup_const A

/-- The value from the starting position `y0`: the infimum of the long-run average cost over
all admissible policies. -/
def valueFrom (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (K y0 : ℝ) : ℝ≥0∞ :=
  ⨅ (U : Type) (_ : MeasurableSpace U) (ν : Measure U) (_ : IsProbabilityMeasure ν)
    (q : SLPolicy U) (_ : SLAdmissible q), slAvgCost ρ f K y0 q ν

lemma valueFrom_le (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (K y0 : ℝ)
    {U : Type} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν] (q : SLPolicy U)
    (hq : SLAdmissible q) : valueFrom ρ f K y0 ≤ slAvgCost ρ f K y0 q ν := by
  unfold valueFrom
  refine iInf_le_of_le U ?_
  refine iInf_le_of_le ‹MeasurableSpace U› ?_
  refine iInf_le_of_le ν ?_
  refine iInf_le_of_le ‹IsProbabilityMeasure ν› ?_
  refine iInf_le_of_le q ?_
  exact iInf_le_of_le hq le_rfl

/-- The value from any starting position is at most the cost of any `(s,S)` policy. -/
lemma value_le_ss (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (K y0 s S : ℝ) (hK : 0 ≤ K) (hsS : s ≤ S) :
    valueFrom ρ f K y0 ≤ ssAvgCost ρ f K s S :=
  (valueFrom_le ρ f K y0 (Measure.dirac ()) (rulePolicy y0 s S)
    (rulePolicy_adm y0 s S hsS)).trans (slAvg_rule_le ρ hρ f hfc hf0 K y0 s S hK hsS)

/-- A bounded subsolution at level `g` bounds the value from below, from every starting
position. -/
lemma value_ge_of_sub (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ)
    (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (K g : ℝ) (v : ℝ → ℝ) (hvm : Measurable v)
    (hvb : ∀ y, -K ≤ v y ∧ v y ≤ 0) (hsub : ∀ y, g ≤ f y + ∫ d, v (y - (d : ℝ)) ∂ρ - v y)
    (y0 : ℝ) : ENNReal.ofReal g ≤ valueFrom ρ f K y0 := by
  unfold valueFrom
  refine le_iInf fun Ut => le_iInf fun ms => le_iInf fun νt => le_iInf fun hν =>
    le_iInf fun qt => le_iInf fun hadm => ?_
  have hb : ∀ T : ℕ, ENNReal.ofReal (T * g) ≤ ∫⁻ ω, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (slPeriodCost f K y0 qt ω.1 (padHist T ω.2) t)
        ∂(νt.prod (Measure.pi fun _ : Fin T => ρ)) + ENNReal.ofReal K := by
    intro T
    exact sl_adapted_bound ρ νt (fun x => x) measurable_id qt hadm.1 hadm.2.1 hadm.2.2 y0 f hfm
      hf0 K g v hvm hvb hsub T T le_rfl
  unfold slAvgCost
  set I : ℕ → ℝ≥0∞ := fun T => ∫⁻ ω, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (slPeriodCost f K y0 qt ω.1 (padHist T ω.2) t)
        ∂(νt.prod (Measure.pi fun _ : Fin T => ρ)) with hI
  have h1 : ∀ T : ℕ, 1 ≤ T →
      ENNReal.ofReal g ≤ (T : ℝ≥0∞)⁻¹ * I T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K := by
    intro T hT
    rw [← mul_add]
    have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    calc ENNReal.ofReal g = (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal (T * g) := by
          rcases le_or_gt 0 g with hg | hg
          · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← mul_assoc,
              ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]
          · rw [ENNReal.ofReal_of_nonpos hg.le, ENNReal.ofReal_of_nonpos
              (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hg.le), mul_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb T) (by positivity)
  have h0 : Tendsto (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using this
  calc ENNReal.ofReal g = limsup (fun _ : ℕ => ENNReal.ofReal g) atTop :=
        (limsup_const (ENNReal.ofReal g)).symm
    _ ≤ limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * I T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop :=
        limsup_le_limsup (eventually_atTop.2 ⟨1, h1⟩)
    _ ≤ limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * I T) atTop :=
        limsup_add_tendsto_zero _ _ h0

/-! ### The bounded subsolution at a level `J` -/

/-- If the cycles that start at the left end `a` of `{f < J}` cost at least `J` (with setup
cost `K`), then there is a bounded subsolution at level `J`. -/
lemma level_subsolution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f)
    (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (K : ℝ) (hK : 0 ≤ K) (J : ℝ) (hJ0 : 0 ≤ J)
    (hcyc : ∀ y, sInf {y | f y < J} < y → y < sSup {y | f y < J} →
      J * (renewalMeasure ρ (Set.Ico 0 (y - sInf {y | f y < J}))).toReal
        ≤ K + ∫ x in Set.Ico 0 (y - sInf {y | f y < J}), f (y - x) ∂(renewalMeasure ρ)) :
    ∃ v : ℝ → ℝ, Measurable v ∧ (∀ y, -K ≤ v y ∧ v y ≤ 0) ∧
      ∀ y, J + max (f y - J) 0 ≤ f y + ∫ d, v (y - (d : ℝ)) ∂ρ - v y := by
  have hSF : SFinite (renewalMeasure ρ) := by unfold renewalMeasure; infer_instance
  have hfm : Measurable f := hfc.measurable
  by_cases hA : ∀ y, J ≤ f y
  · refine ⟨fun _ => 0, measurable_const, fun y => ⟨by linarith, le_rfl⟩, fun y => ?_⟩
    have h1 : max (f y - J) 0 = f y - J := max_eq_left (by linarith [hA y])
    simp only [integral_zero, sub_zero, add_zero, h1]
    linarith
  simp only [not_forall, not_le] at hA
  obtain ⟨y0, hy0⟩ := hA
  -- the interval `{f < J} = (a, b)`
  set A : Set ℝ := {y | f y < J} with hAdef
  obtain ⟨R, hR⟩ := hfco J
  have hAR : ∀ y ∈ A, |y| < R := fun y hy => by
    by_contra h
    exact absurd (hR y (not_lt.1 h)) (not_le.2 hy)
  have hAne : A.Nonempty := ⟨y0, hy0⟩
  have hAbb : BddBelow A := ⟨-R, fun y hy => by
    have := hAR y hy
    linarith [neg_abs_le y]⟩
  have hAba : BddAbove A := ⟨R, fun y hy => by
    have := hAR y hy
    linarith [le_abs_self y]⟩
  have hAopen : IsOpen A := isOpen_lt hfc continuous_const
  set a := sInf A with ha
  set b := sSup A with hb
  have ha_notin : a ∉ A := by
    intro haA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAopen a haA
    have hmem : a - ε / 2 ∈ A := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
      linarith)
    have := csInf_le hAbb hmem
    linarith
  have hb_notin : b ∉ A := by
    intro hbA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAopen b hbA
    have hmem : b + ε / 2 ∈ A := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith)
    have := le_csSup hAba hmem
    linarith
  have hK1 : ∀ y, y ≤ a → J ≤ f y := by
    intro y hy
    by_contra h
    have hyA : y ∈ A := not_le.1 h
    have hya : y = a := le_antisymm hy (csInf_le hAbb hyA)
    rw [hya] at hyA
    exact ha_notin hyA
  have hK2 : ∀ y, b ≤ y → J ≤ f y := by
    intro y hy
    by_contra h
    have hyA : y ∈ A := not_le.1 h
    have hyb : y = b := le_antisymm (le_csSup hAba hyA) hy
    rw [hyb] at hyA
    exact hb_notin hyA
  have hK3 : ∀ y, a < y → y < b → f y < J := by
    intro y h1 h2
    obtain ⟨y1, hy1A, hy1⟩ := exists_lt_of_csInf_lt hAne h1
    obtain ⟨y2, hy2A, hy2⟩ := exists_lt_of_lt_csSup hAne h2
    exact lt_of_le_of_lt (hfcv.le_max_of_mem_Icc (Set.mem_univ y1) (Set.mem_univ y2)
      ⟨hy1.le, hy2.le⟩) (max_lt hy1A hy2A)
  have hab : a < b := by
    have h1 : a ≤ y0 := csInf_le hAbb hy0
    have h2 : y0 ≤ b := le_csSup hAba hy0
    have h3 : a ≠ y0 := fun h => ha_notin (h ▸ hy0)
    exact lt_of_lt_of_le (lt_of_le_of_ne h1 h3) h2
  -- the expected cost and count of the periods before the position falls to `a`
  have hUfin : ∀ w, renewalMeasure ρ (Set.Ico 0 w) ≠ ∞ := fun w =>
    (renewalMeasure_Ico_lt_top ρ hρ w).ne
  set Λ : ℝ → ℝ≥0∞ := fun y => ∫⁻ z in Set.Ico 0 (y - a), ENNReal.ofReal (f (y - z))
    ∂(renewalMeasure ρ) with hΛ
  set Nw : ℝ → ℝ≥0∞ := fun y => renewalMeasure ρ (Set.Ico 0 (y - a)) with hNw
  have hΛm : Measurable Λ := by
    have : Λ = fun y => ∫⁻ z, ({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < p.1 - a}.indicator
        (fun p => ENNReal.ofReal (f (p.1 - p.2)))) (y, z) ∂(renewalMeasure ρ) := by
      funext y
      rw [hΛ]
      simp only
      rw [← lintegral_indicator measurableSet_Ico]
      rfl
    rw [this]
    refine Measurable.lintegral_prod_right' (Measurable.indicator ?_ ?_)
    · exact ENNReal.measurable_ofReal.comp (hfm.comp (measurable_fst.sub measurable_snd))
    · exact (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_fst.sub measurable_const))
  have hNm : Measurable Nw := by
    have : Nw = fun y => ∫⁻ z, ({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < p.1 - a}.indicator 1) (y, z)
        ∂(renewalMeasure ρ) := by
      funext y
      rw [hNw]
      simp only
      rw [← lintegral_indicator_one measurableSet_Ico]
      rfl
    rw [this]
    refine Measurable.lintegral_prod_right' (Measurable.indicator measurable_const ?_)
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.sub measurable_const))
  have hCbd : ∀ y, ∃ C, 0 ≤ C ∧ ∀ x ∈ Set.Icc a y, f x ≤ C := fun y => by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := y)).exists_bound_of_continuousOn
      hfc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have h1 : |f x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hx
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  have hNle : ∀ y y', y' ≤ y → Nw y' ≤ Nw y := fun y y' h =>
    measure_mono (Set.Ico_subset_Ico_right (by linarith))
  have hΛle : ∀ y y' C, y' ≤ y → (∀ x ∈ Set.Icc a y, f x ≤ C) → 0 ≤ C →
      Λ y' ≤ ENNReal.ofReal C * Nw y := by
    intro y y' C hy hC hC0
    calc Λ y' ≤ ∫⁻ _z in Set.Ico 0 (y' - a), ENNReal.ofReal C ∂(renewalMeasure ρ) := by
          refine setLIntegral_mono' measurableSet_Ico fun z hz => ENNReal.ofReal_le_ofReal ?_
          exact hC _ ⟨by linarith [hz.2], by linarith [hz.1]⟩
      _ = ENNReal.ofReal C * Nw y' := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * Nw y := by gcongr; exact hNle y y' hy
  have hNfin : ∀ y, Nw y ≠ ∞ := fun y => hUfin _
  have hΛfin : ∀ y, Λ y ≠ ∞ := fun y => by
    obtain ⟨C, hC0, hC⟩ := hCbd y
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y))
      (hΛle y y C le_rfl hC hC0)
  -- the relative value `k(y) = K + ∫_{[0,y-a)} (f(y-z) - J) U(dz)`
  set kk : ℝ → ℝ := fun y => K + (Λ y).toReal - J * (Nw y).toReal with hkk
  have hkkm : Measurable kk :=
    (measurable_const.add hΛm.ennreal_toReal).sub (measurable_const.mul hNm.ennreal_toReal)
  have hkk_le : ∀ y, y ≤ a → kk y = K := by
    intro y hy
    have he : Set.Ico (0 : ℝ) (y - a) = ∅ := Set.Ico_eq_empty (by linarith)
    simp only [hkk, hΛ, hNw, he, Measure.restrict_empty, lintegral_zero_measure, measure_empty,
      ENNReal.toReal_zero, mul_zero, add_zero, sub_zero]
  have hkk_upper : ∀ y, a < y → y < b → kk y ≤ K := by
    intro y h1 h2
    have hle : Λ y ≤ ENNReal.ofReal J * Nw y := by
      calc Λ y ≤ ∫⁻ _z in Set.Ico 0 (y - a), ENNReal.ofReal J ∂(renewalMeasure ρ) := by
            refine setLIntegral_mono' measurableSet_Ico fun z hz => ENNReal.ofReal_le_ofReal ?_
            exact (hK3 _ (by linarith [hz.2]) (by linarith [hz.1])).le
        _ = ENNReal.ofReal J * Nw y := setLIntegral_const _ _
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y)) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ0] at this
    simp only [hkk]
    linarith
  have hNpos : ∀ y, a < y → 1 ≤ (Nw y).toReal := by
    intro y hy
    have := ENNReal.toReal_mono (hNfin y) (one_le_renewal ρ (y - a) (by linarith))
    simpa using this
  have hInt : ∀ y, (∫ x in Set.Ico 0 (y - a), f (y - x) ∂(renewalMeasure ρ)) = (Λ y).toReal := by
    intro y
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => f (y - x)) (ae_of_all _ fun x => hf0 _)
      (hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
  have hkk_nonneg : ∀ y, a < y → y < b → 0 ≤ kk y := by
    intro y hy hyb
    have h := hcyc y hy hyb
    rw [hInt y] at h
    simp only [hkk]
    linarith
  -- the renewal equations
  have hΛeq : ∀ y, a < y → Λ y = ENNReal.ofReal (f y) + ∫⁻ d, Λ (y - d) ∂ρ := by
    intro y hy
    have hG : Measurable fun z : ℝ => ENNReal.ofReal (f (y - z)) :=
      ENNReal.measurable_ofReal.comp (hfm.comp (measurable_const.sub measurable_id))
    have h := renewal_window ρ (y - a) hG 0 le_rfl (by linarith)
    simp only [sub_zero, zero_add] at h
    simp only [hΛ]
    rw [h]
    congr 1
    refine lintegral_congr fun d => ?_
    rw [show y - (d : ℝ) - a = y - a - d by ring]
    refine lintegral_congr fun u => ?_
    rw [show y - ((d : ℝ) + u) = y - d - u by ring]
  have hNeq : ∀ y, a < y → Nw y = 1 + ∫⁻ d, Nw (y - d) ∂ρ := by
    intro y hy
    have h := renewal_window ρ (y - a) (G := fun _ => (1 : ℝ≥0∞)) measurable_const 0 le_rfl
      (by linarith)
    simp only [sub_zero, zero_add, setLIntegral_one] at h
    simp only [hNw]
    rw [h]
    congr 1
    refine lintegral_congr fun d => ?_
    rw [show y - (d : ℝ) - a = y - a - d by ring]
  have hiΛ : ∀ y, Integrable (fun d : ℝ≥0 => (Λ (y - d)).toReal) ρ := by
    intro y
    obtain ⟨C, hC0, hC⟩ := hCbd y
    refine Integrable.of_bound (hΛm.comp (measurable_const.sub
      measurable_coe_nnreal_real)).ennreal_toReal.aestronglyMeasurable (C * (Nw y).toReal)
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y))
      (hΛle y (y - d) C (by linarith [NNReal.coe_nonneg d]) hC hC0)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at this
  have hiN : ∀ y, Integrable (fun d : ℝ≥0 => (Nw (y - d)).toReal) ρ := by
    intro y
    refine Integrable.of_bound (hNm.comp (measurable_const.sub
      measurable_coe_nnreal_real)).ennreal_toReal.aestronglyMeasurable (Nw y).toReal
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (hNfin y) (hNle y (y - d) (by linarith [NNReal.coe_nonneg d]))
  have hikk : ∀ y, Integrable (fun d : ℝ≥0 => kk (y - d)) ρ := fun y =>
    ((integrable_const K).add (hiΛ y)).sub ((hiN y).const_mul J)
  have hkkeq : ∀ y, a < y → kk y = f y - J + ∫ d, kk (y - d) ∂ρ := by
    intro y hy
    have hΛm' : Measurable fun d : ℝ≥0 => Λ (y - d) :=
      hΛm.comp (measurable_const.sub measurable_coe_nnreal_real)
    have hNm' : Measurable fun d : ℝ≥0 => Nw (y - d) :=
      hNm.comp (measurable_const.sub measurable_coe_nnreal_real)
    have hΛint : (∫⁻ d, Λ (y - d) ∂ρ).toReal = ∫ d, (Λ (y - d)).toReal ∂ρ :=
      (integral_toReal hΛm'.aemeasurable (ae_of_all _ fun d => (hΛfin _).lt_top)).symm
    have hNint : (∫⁻ d, Nw (y - d) ∂ρ).toReal = ∫ d, (Nw (y - d)).toReal ∂ρ :=
      (integral_toReal hNm'.aemeasurable (ae_of_all _ fun d => (hNfin _).lt_top)).symm
    have hΛfin' : ∫⁻ d, Λ (y - d) ∂ρ ≠ ∞ := fun htop =>
      hΛfin y (by rw [hΛeq y hy, htop, add_top])
    have hNfin' : ∫⁻ d, Nw (y - d) ∂ρ ≠ ∞ := fun htop =>
      hNfin y (by rw [hNeq y hy, htop, add_top])
    have e1 : (Λ y).toReal = f y + ∫ d, (Λ (y - d)).toReal ∂ρ := by
      rw [hΛeq y hy, ENNReal.toReal_add ENNReal.ofReal_ne_top hΛfin',
        ENNReal.toReal_ofReal (hf0 _), hΛint]
    have e2 : (Nw y).toReal = 1 + ∫ d, (Nw (y - d)).toReal ∂ρ := by
      rw [hNeq y hy, ENNReal.toReal_add ENNReal.one_ne_top hNfin', ENNReal.toReal_one, hNint]
    have e3 : ∫ d, kk (y - d) ∂ρ
        = K + ∫ d, (Λ (y - d)).toReal ∂ρ - J * ∫ d, (Nw (y - d)).toReal ∂ρ := by
      simp only [hkk]
      have i1 : Integrable (fun d : ℝ≥0 => K + (Λ (y - d)).toReal) ρ :=
        (integrable_const K).add (hiΛ y)
      have i2 : Integrable (fun d : ℝ≥0 => J * (Nw (y - d)).toReal) ρ := (hiN y).const_mul J
      rw [integral_sub i1 i2, integral_add (integrable_const K) (hiΛ y), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    rw [e3]
    simp only [hkk]
    rw [e1, e2]
    ring
  -- the bounded relative value `v`
  set v : ℝ → ℝ := fun y => if y < b then kk y - K else -K with hv
  have hvm : Measurable v :=
    Measurable.ite measurableSet_Iio (hkkm.sub measurable_const) measurable_const
  have hvb : ∀ y, -K ≤ v y ∧ v y ≤ 0 := by
    intro y
    simp only [hv]
    split_ifs with h
    · rcases le_or_gt y a with h' | h'
      · rw [hkk_le y h']
        constructor <;> linarith
      · have := hkk_nonneg y h' h
        have := hkk_upper y h' h
        constructor <;> linarith
    · constructor <;> linarith
  have hvint : ∀ y, Integrable (fun d : ℝ≥0 => v (y - d)) ρ := by
    intro y
    refine Integrable.of_bound (hvm.comp (measurable_const.sub
      measurable_coe_nnreal_real)).aestronglyMeasurable K (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(hvb _).1, by linarith [(hvb (y - (d : ℝ))).2]⟩
  refine ⟨v, hvm, hvb, fun y => ?_⟩
  rcases le_or_gt y a with hya | hya
  · -- at or below `a`: no relative value, and `f ≥ J`
    have hfy := hK1 y hya
    have hv0 : (fun d : ℝ≥0 => v (y - d)) = fun _ => 0 := by
      funext d
      have h1 : y - (d : ℝ) ≤ a := by linarith [NNReal.coe_nonneg d]
      simp only [hv, if_pos (show y - (d : ℝ) < b by linarith), hkk_le _ h1, sub_self]
    have hvy : v y = 0 := by
      simp only [hv, if_pos (show y < b by linarith), hkk_le _ hya, sub_self]
    rw [hv0, integral_zero, hvy, max_eq_left (by linarith)]
    linarith
  rcases lt_or_ge y b with hyb | hyb
  · -- inside `(a, b)`: the Poisson equation gives equality
    have hfy := hK3 y hya hyb
    have hvd : (fun d : ℝ≥0 => v (y - d)) = fun d : ℝ≥0 => kk (y - d) - K := by
      funext d
      simp only [hv, if_pos (show y - (d : ℝ) < b by linarith [NNReal.coe_nonneg d])]
    have hvy : v y = kk y - K := by simp only [hv, if_pos hyb]
    have hI : ∫ d, v (y - (d : ℝ)) ∂ρ = ∫ d, kk (y - d) ∂ρ - K := by
      rw [hvd, integral_sub (hikk y) (integrable_const K), integral_const, probReal_univ,
        one_smul]
    rw [hI, hvy, max_eq_right (by linarith)]
    have := hkkeq y hya
    linarith
  · -- at or above `b`: the relative value is at its minimum `-K`
    have hfy := hK2 y hyb
    have hvy : v y = -K := by simp only [hv, if_neg (not_lt.2 hyb)]
    have hge : -K ≤ ∫ d, v (y - (d : ℝ)) ∂ρ := by
      have := integral_mono (integrable_const (-K)) (hvint y) (fun d => (hvb (y - d)).1)
      simpa [integral_const, probReal_univ] using this
    rw [hvy, max_eq_left (by linarith)]
    linarith

/-! ### Integrals over windows of the renewal measure -/

lemma intOn_Ico (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w : ℝ) :
    IntegrableOn F (Set.Ico 0 w) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := w)).exists_bound_of_continuousOn
    hF.continuousOn
  exact Measure.integrableOn_of_bounded (renewalMeasure_Ico_lt_top ρ hρ w).ne
    hF.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ico fun x hx =>
      hC x (Set.Ico_subset_Icc_self hx))

lemma int_sub_const (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w c : ℝ) :
    ∫ x in Set.Ico 0 w, (F x - c) ∂(renewalMeasure ρ)
      = ∫ x in Set.Ico 0 w, F x ∂(renewalMeasure ρ)
        - c * (renewalMeasure ρ (Set.Ico 0 w)).toReal := by
  rw [integral_sub (intOn_Ico ρ hρ F hF w)
    (integrableOn_const (renewalMeasure_Ico_lt_top ρ hρ w).ne), setIntegral_const, smul_eq_mul,
    measureReal_def, mul_comm]

lemma int_ge_const (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w c : ℝ) (h : ∀ x ∈ Set.Ico 0 w, c ≤ F x) :
    c * (renewalMeasure ρ (Set.Ico 0 w)).toReal
      ≤ ∫ x in Set.Ico 0 w, F x ∂(renewalMeasure ρ) := by
  have h1 := setIntegral_mono_on
    (integrableOn_const (C := c) (renewalMeasure_Ico_lt_top ρ hρ w).ne)
    (intOn_Ico ρ hρ F hF w) measurableSet_Ico h
  rwa [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm] at h1

lemma renewal_toReal_mono (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) {w w' : ℝ} (h : w ≤ w') :
    (renewalMeasure ρ (Set.Ico 0 w)).toReal ≤ (renewalMeasure ρ (Set.Ico 0 w')).toReal :=
  ENNReal.toReal_mono (renewalMeasure_Ico_lt_top ρ hρ w').ne
    (measure_mono (Set.Ico_subset_Ico_right h))

lemma one_le_renewal_toReal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) {w : ℝ} (hw : 0 < w) :
    1 ≤ (renewalMeasure ρ (Set.Ico 0 w)).toReal := by
  have := ENNReal.toReal_mono (renewalMeasure_Ico_lt_top ρ hρ w).ne (one_le_renewal ρ w hw)
  simpa using this

/-! ### Levels -/

/-- If the cycles started at the left end of `{f < g}` cost at least `g`, the value from every
starting position is at least `g`. -/
lemma value_ge_level (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f)
    (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (K : ℝ) (hK : 0 ≤ K) (g : ℝ) (hg0 : 0 ≤ g)
    (hcyc : ∀ y, sInf {y | f y < g} < y → y < sSup {y | f y < g} →
      0 ≤ K + ∫ x in Set.Ico 0 (y - sInf {y | f y < g}), (f (y - x) - g) ∂(renewalMeasure ρ))
    (y0 : ℝ) : ENNReal.ofReal g ≤ valueFrom ρ f K y0 := by
  obtain ⟨v, hvm, hvb, hsub⟩ := level_subsolution ρ hρ f hfc hfcv hf0 hfco K hK g hg0
    (fun y h1 h2 => by
      have := hcyc y h1 h2
      rw [int_sub_const ρ hρ (fun x => f (y - x)) (hfc.comp (continuous_const.sub continuous_id))]
        at this
      linarith)
  exact value_ge_of_sub ρ f hfc.measurable hf0 K g v hvm hvb
    (fun y => le_trans (le_add_of_nonneg_right (le_max_right _ _)) (hsub y)) y0

lemma level_le (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f)
    (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (K : ℝ) (hK : 0 ≤ K) (J : ℝ) (hJ0 : 0 ≤ J)
    (hval : valueFrom ρ f K 0 = ENNReal.ofReal J) (g : ℝ) (hg0 : 0 ≤ g)
    (hcyc : ∀ y, sInf {y | f y < g} < y → y < sSup {y | f y < g} →
      0 ≤ K + ∫ x in Set.Ico 0 (y - sInf {y | f y < g}), (f (y - x) - g) ∂(renewalMeasure ρ)) :
    g ≤ J := by
  have h := value_ge_level ρ hρ f hfc hfcv hf0 hfco K hK g hg0 hcyc 0
  rw [hval] at h
  exact (ENNReal.ofReal_le_ofReal_iff hJ0).1 h

/-! ### Base stock -/

section coord
variable {α : Type} [MeasurableSpace α] [Zero α]
lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const
end coord

lemma ssPre_SS_le (S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre S S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) ≤ S
    rw [if_pos (ssPre_SS_le S d t)]
    linarith [NNReal.coe_nonneg (d t)]

lemma ssPeriodCost_SS (f : ℝ → ℝ) (K S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    ssPeriodCost f K S S d t
      = (if t = 0 then 0 else K * (if 0 < d (t - 1) then 1 else 0)) + f S := by
  unfold ssPeriodCost ssPost
  rw [if_pos (ssPre_SS_le S d t)]
  cases t with
  | zero => simp [ssPre]
  | succ t =>
    have h : ssPre S S d (t + 1) = S - (d t : ℝ) := by
      show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) = _
      rw [if_pos (ssPre_SS_le S d t)]
    rw [h, if_neg (Nat.succ_ne_zero t), add_tsub_cancel_right]
    congr 2
    by_cases hd : 0 < d t
    · have : (0 : ℝ) < (d t : ℝ) := by exact_mod_cast hd
      rw [if_pos ⟨by linarith, by linarith⟩, if_pos hd]
    · have : (d t : ℝ) = 0 := by
        have := le_antisymm (not_lt.1 hd) zero_le
        exact_mod_cast this
      rw [if_neg (by rw [this]; simp), if_neg hd]

/-- The long-run average cost of the base-stock policy `(S,S)`. -/
lemma ss_avg_SS (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (K S : ℝ) (hK : 0 ≤ K) :
    ssAvgCost ρ f K S S = ENNReal.ofReal (f S + K * (ρ (Set.Ioi 0)).toReal) := by
  set r := (ρ (Set.Ioi 0)).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hint : ∫ a, (K * (if 0 < a then 1 else 0) + f S) ∂ρ = K * r + f S := by
    have h1 : (fun a : ℝ≥0 => K * (if 0 < a then (1 : ℝ) else 0) + f S)
        = fun a => K * (Set.Ioi (0 : ℝ≥0)).indicator 1 a + f S := by
      funext a
      by_cases ha : 0 < a
      · simp [Set.indicator_of_mem (show a ∈ Set.Ioi 0 from ha), ha]
      · simp [Set.indicator_of_notMem (show a ∉ Set.Ioi 0 from ha), ha]
    have hi1 : Integrable ((Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ)) ρ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
    rw [h1, integral_add (f := fun a => K * (Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ) a)
      (hi1.const_mul K) (integrable_const _), integral_const_mul,
      integral_indicator_one measurableSet_Ioi, integral_const, probReal_univ, one_smul,
      measureReal_def]
  have hE : ∀ T t, t < T →
      ∫⁻ z, ENNReal.ofReal (ssPeriodCost f K S S (padHist T z) t) ∂(Measure.pi fun _ : Fin T => ρ)
        = ENNReal.ofReal ((if t = 0 then 0 else K * r) + f S) := by
    intro T t ht
    simp_rw [ssPeriodCost_SS]
    rcases t with _ | t
    · simp
    · have hcoord : ∀ z : Fin T → ℝ≥0, padHist T z t = z ⟨t, by omega⟩ := fun z => by
        simp [padHist, show t < T by omega]
      simp only [Nat.succ_ne_zero, if_false, add_tsub_cancel_right, hcoord]
      have hmp := measurePreserving_eval (fun _ : Fin T => ρ) (⟨t, by omega⟩ : Fin T)
      have hm : Measurable fun a : ℝ≥0 => ENNReal.ofReal (K * (if 0 < a then 1 else 0) + f S) :=
        ENNReal.measurable_ofReal.comp ((measurable_const.mul (Measurable.ite measurableSet_Ioi
          measurable_const measurable_const)).add measurable_const)
      rw [hmp.lintegral_comp hm, ← ofReal_integral_eq_lintegral_ofReal, hint]
      · refine Integrable.of_bound (C := K + f S) ((measurable_const.mul (Measurable.ite
          (measurableSet_lt measurable_const measurable_id) measurable_const
          measurable_const)).add measurable_const).aestronglyMeasurable (ae_of_all _ fun a => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := hf0 S; split_ifs <;> nlinarith)]
        split_ifs <;> linarith
      · exact ae_of_all _ fun a => by
          simp only [Pi.zero_apply]; have := hf0 S; split_ifs <;> nlinarith
  have havg : ∀ T : ℕ, ((T + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range (T + 1),
      ENNReal.ofReal (ssPeriodCost f K S S (padHist (T + 1) z) t) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
        = ENNReal.ofReal (f S + K * r * ((T : ℝ) / ((T : ℝ) + 1))) := by
    intro T
    rw [lintegral_finsetSum]
    · rw [Finset.sum_congr rfl fun t ht => hE (T + 1) t (Finset.mem_range.1 ht),
        ← ENNReal.ofReal_sum_of_nonneg (fun t _ => by have := hf0 S; split_ifs <;> nlinarith)]
      have hsum : ∑ t ∈ Finset.range (T + 1), ((if t = 0 then 0 else K * r) + f S)
          = (T : ℝ) * (K * r) + ((T : ℝ) + 1) * f S := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, if_true, zero_add, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      rw [hsum]
      have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      rw [show ((T + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((T : ℝ) + 1) by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
        ← ENNReal.ofReal_inv_of_pos hT, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    · intro t _
      exact ENNReal.measurable_ofReal.comp (by
        have hp := measurable_padHist' (α := ℝ≥0) (T + 1)
        simp_rw [ssPeriodCost_SS]
        refine Measurable.add ?_ measurable_const
        split_ifs
        · exact measurable_const
        · exact measurable_const.mul (Measurable.ite
            (measurableSet_lt measurable_const ((measurable_pi_apply (t - 1)).comp hp))
            measurable_const measurable_const))
  have hlim : Tendsto (fun T : ℕ => ENNReal.ofReal (f S + K * r * ((T : ℝ) / ((T : ℝ) + 1))))
      atTop (𝓝 (ENNReal.ofReal (f S + K * r))) := by
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul (K * r)
    simpa using this.const_add (f S)
  unfold ssAvgCost
  refine Tendsto.limsup_eq ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hlim.congr fun T => ?_
  rw [havg T]


/-! ### The cycle length of the `(s,S)` policy -/

lemma ssPre_le_S (s S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre s S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    have ih := ssPre_le_S s S d t
    show (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ) ≤ S
    split_ifs <;> linarith [NNReal.coe_nonneg (d t)]

lemma ssPost_mem (s S : ℝ) (hsS : s < S) (d : ℕ → ℝ≥0) (t : ℕ) :
    s < ssPost s S d t ∧ ssPost s S d t ≤ S := by
  unfold ssPost
  split_ifs with h
  · exact ⟨hsS, le_rfl⟩
  · exact ⟨not_le.1 h, ssPre_le_S s S d t⟩

/-- Before the first reorder, the pre-action position is `S` minus the cumulative demand. -/
lemma ssPre_eq_of_no_reorder (s S : ℝ) (hsS : s < S) (d : ℕ → ℝ≥0) (n : ℕ)
    (hn : ∀ t, 1 ≤ t → t < n → s < ssPre s S d t) :
    ∀ t, t ≤ n → ssPre s S d t = S - ∑ r ∈ Finset.range t, (d r : ℝ)
  | 0, _ => by simp [ssPre]
  | t + 1, ht => by
    have ih := ssPre_eq_of_no_reorder s S hsS d n hn t (by omega)
    have hpos : s < ssPre s S d t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        show s < S
        exact hsS
      · exact hn t h0 (by omega)
    show (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ) = _
    rw [if_neg (not_le.2 hpos), ih, Finset.sum_range_succ]
    ring

/-- The cycle length (the time of the first reorder) of the `(s,S)` policy started at `S`. -/
def cycLen (s S : ℝ) (d : ℕ → ℝ≥0) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : 1 ≤ t ∧ ssPre s S d t ≤ s), (t : ℝ≥0∞)

lemma cycLen_pow_le (s S : ℝ) (hsS : s < S) (m : ℕ) (d : ℕ → ℝ≥0) :
    cycLen s S d ^ m ≤ ∑' t : ℕ, ((t : ℝ≥0∞) + 1) ^ m *
      Set.indicator {d : ℕ → ℝ≥0 | ∑ r ∈ Finset.range t, (d r : ℝ) < S - s} 1 d := by
  classical
  by_cases hex : ∃ n, 1 ≤ n ∧ ssPre s S d n ≤ s
  · have hn : 1 ≤ Nat.find hex ∧ ssPre s S d (Nat.find hex) ≤ s := Nat.find_spec hex
    have hmin : ∀ t, 1 ≤ t → t < Nat.find hex → s < ssPre s S d t := fun t h1 h2 =>
      not_le.1 fun h => Nat.find_min hex h2 ⟨h1, h⟩
    have hτ : cycLen s S d ≤ (Nat.find hex : ℝ≥0∞) :=
      iInf_le_of_le (Nat.find hex) (iInf_le_of_le hn le_rfl)
    have hmem : d ∈ {d : ℕ → ℝ≥0 | ∑ r ∈ Finset.range (Nat.find hex - 1), (d r : ℝ) < S - s} := by
      have he := ssPre_eq_of_no_reorder s S hsS d (Nat.find hex) hmin (Nat.find hex - 1)
        (by omega)
      show ∑ r ∈ Finset.range (Nat.find hex - 1), (d r : ℝ) < S - s
      rcases Nat.eq_zero_or_pos (Nat.find hex - 1) with h0 | h0
      · rw [h0, Finset.sum_range_zero]
        linarith
      · have := hmin (Nat.find hex - 1) h0 (by omega)
        linarith
    have hcast : (Nat.find hex : ℝ≥0∞) = ((Nat.find hex - 1 : ℕ) : ℝ≥0∞) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hn.1).symm
    calc cycLen s S d ^ m ≤ (Nat.find hex : ℝ≥0∞) ^ m := pow_le_pow_left₀ (by positivity) hτ m
      _ = (((Nat.find hex - 1 : ℕ) : ℝ≥0∞) + 1) ^ m * Set.indicator
            {d : ℕ → ℝ≥0 | ∑ r ∈ Finset.range (Nat.find hex - 1), (d r : ℝ) < S - s} 1 d := by
          rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, hcast]
      _ ≤ _ := ENNReal.le_tsum (Nat.find hex - 1)
  · push_neg at hex
    have hall : ∀ t, d ∈ {d : ℕ → ℝ≥0 | ∑ r ∈ Finset.range t, (d r : ℝ) < S - s} := by
      intro t
      have he := ssPre_eq_of_no_reorder s S hsS d (t + 1) (fun r h1 _ => hex r h1) t (by omega)
      show ∑ r ∈ Finset.range t, (d r : ℝ) < S - s
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        rw [Finset.sum_range_zero]
        linarith
      · have := hex t h0
        linarith
    have htop : ∑' t : ℕ, ((t : ℝ≥0∞) + 1) ^ m * Set.indicator
        {d : ℕ → ℝ≥0 | ∑ r ∈ Finset.range t, (d r : ℝ) < S - s} 1 d = ⊤ := by
      refine top_unique ?_
      calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
        _ ≤ _ := ENNReal.tsum_le_tsum fun t => by
          rw [Set.indicator_of_mem (hall t), Pi.one_apply, mul_one]
          exact one_le_pow₀ le_add_self
    rw [htop]
    exact le_top

/-- The cycle length has finite moments of every order. -/
lemma cycLen_moment (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (s S : ℝ) (hsS : s < S) (m : ℕ) :
    ∫⁻ d, cycLen s S d ^ m ∂(Measure.infinitePi fun _ : ℕ => ρ) < ∞ := by
  set P := Measure.infinitePi fun _ : ℕ => ρ with hP
  set w := S - s with hw
  set E : ℕ → Set (ℕ → ℝ≥0) := fun t => {d | ∑ r ∈ Finset.range t, (d r : ℝ) < w} with hE
  have hEm : ∀ t, MeasurableSet (E t) := fun t =>
    measurableSet_lt (Finset.measurable_sum _ fun r _ =>
      (measurable_pi_apply r).coe_nnreal_real) measurable_const
  set φ : ℝ≥0 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(x : ℝ))) with hφ
  have hφm : Measurable φ :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_coe_nnreal_real.neg)
  set θ := ∫⁻ x, φ x ∂ρ with hθ
  -- `θ = E e^{-D} < 1`
  have hθ1 : θ < 1 := by
    set ψ : ℝ≥0 → ℝ≥0∞ := fun x => ENNReal.ofReal (1 - Real.exp (-(x : ℝ))) with hψ
    have hψm : Measurable ψ := ENNReal.measurable_ofReal.comp
      (measurable_const.sub (Real.measurable_exp.comp measurable_coe_nnreal_real.neg))
    have hsum : θ + ∫⁻ x, ψ x ∂ρ = 1 := by
      rw [hθ, ← lintegral_add_left hφm]
      have h1 : ∀ x : ℝ≥0, φ x + ψ x = 1 := fun x => by
        have hle : Real.exp (-(x : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 x.2)
        simp only [hφ, hψ]
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by linarith)]
        simp
      simp only [h1, lintegral_const, measure_univ, mul_one]
    have hψ0 : ∫⁻ x, ψ x ∂ρ ≠ 0 := by
      intro h0
      rw [lintegral_eq_zero_iff hψm] at h0
      have hx0 : ∫⁻ x, (x : ℝ≥0∞) ∂ρ = 0 := by
        rw [lintegral_eq_zero_iff measurable_coe_nnreal_ennreal]
        filter_upwards [h0] with x hx
        simp only [hψ, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
        have h1 : 1 ≤ Real.exp (-(x : ℝ)) := by linarith
        have h2 : 0 ≤ -(x : ℝ) := Real.one_le_exp_iff.1 h1
        have h3 : (x : ℝ) = 0 := le_antisymm (by linarith) x.2
        have h4 : x = 0 := by exact_mod_cast h3
        simp [h4]
      rw [hx0] at hρ
      exact lt_irrefl 0 hρ
    have hθfin : θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
    calc θ < θ + ∫⁻ x, ψ x ∂ρ := ENNReal.lt_add_right hθfin hψ0
      _ = 1 := hsum
  -- Chernoff: `P(D_0 + ... + D_{t-1} < w) ≤ e^w θ^t`
  have hPE : ∀ t, P (E t) ≤ ENNReal.ofReal (Real.exp w) * θ ^ t := by
    intro t
    have hle : ∀ d, (E t).indicator 1 d
        ≤ ENNReal.ofReal (Real.exp w) * ∏ r ∈ Finset.range t, φ (d r) := by
      intro d
      by_cases hd : d ∈ E t
      · rw [Set.indicator_of_mem hd, Pi.one_apply]
        have hprod : ENNReal.ofReal (Real.exp w) * ∏ r ∈ Finset.range t, φ (d r)
            = ENNReal.ofReal (Real.exp (w - ∑ r ∈ Finset.range t, (d r : ℝ))) := by
          rw [sub_eq_add_neg, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum,
            ENNReal.ofReal_mul (Real.exp_pos _).le,
            ENNReal.ofReal_prod_of_nonneg (fun r _ => (Real.exp_pos _).le)]
        rw [hprod, ← ENNReal.ofReal_one]
        have : 0 < w - ∑ r ∈ Finset.range t, (d r : ℝ) := by
          have h' : ∑ r ∈ Finset.range t, (d r : ℝ) < w := hd
          linarith
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp this.le)
      · rw [Set.indicator_of_notMem hd]
        positivity
    have hprodm : Measurable fun d : ℕ → ℝ≥0 => ∏ r ∈ Finset.range t, φ (d r) :=
      Finset.measurable_prod _ fun r _ => hφm.comp (measurable_pi_apply r)
    calc P (E t) = ∫⁻ d, (E t).indicator 1 d ∂P := (lintegral_indicator_one (hEm t)).symm
      _ ≤ ∫⁻ d, ENNReal.ofReal (Real.exp w) * ∏ r ∈ Finset.range t, φ (d r) ∂P :=
          lintegral_mono hle
      _ = ENNReal.ofReal (Real.exp w) * ∫⁻ d, ∏ r ∈ Finset.range t, φ (d r) ∂P :=
          lintegral_const_mul _ hprodm
      _ = ENNReal.ofReal (Real.exp w) * θ ^ t := by
          congr 1
          have hind : iIndepFun (fun r (d : ℕ → ℝ≥0) => φ (d r)) P :=
            iIndepFun_infinitePi (P := fun _ : ℕ => ρ) (X := fun _ => φ) (fun _ => hφm)
          rw [lintegral_prod_eq_prod_lintegral_of_indepFun (Finset.range t)
            (fun r (d : ℕ → ℝ≥0) => φ (d r)) hind (fun r => hφm.comp (measurable_pi_apply r))]
          have hr : ∀ r ∈ Finset.range t, ∫⁻ d, φ (d r) ∂P = θ := fun r _ =>
            (measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) r).lintegral_comp hφm
          rw [Finset.prod_congr rfl hr, Finset.prod_const, Finset.card_range]
  -- summation
  have hθfin : θ ≠ ⊤ := ne_top_of_lt hθ1
  set θr := θ.toReal with hθr
  have hθr0 : 0 ≤ θr := ENNReal.toReal_nonneg
  have hθr1 : θr < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hθ1
    simpa using this
  have hb : ∀ t : ℕ, ((t : ℝ) + 1) ^ m ≤ 2 ^ m * ((t : ℝ) ^ m + 1) := by
    intro t
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      have h1 : (0 : ℝ) ≤ (0 : ℝ) ^ m := pow_nonneg le_rfl m
      have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      simp only [Nat.cast_zero, zero_add, one_pow]
      nlinarith
    · have h1 : (t : ℝ) + 1 ≤ 2 * t := by
        have : (1 : ℝ) ≤ t := by exact_mod_cast h
        linarith
      have h2 : (0 : ℝ) ≤ 2 ^ m := pow_nonneg (by norm_num) m
      calc ((t : ℝ) + 1) ^ m ≤ (2 * t) ^ m := pow_le_pow_left₀ (by positivity) h1 m
        _ = 2 ^ m * (t : ℝ) ^ m := mul_pow 2 (t : ℝ) m
        _ ≤ 2 ^ m * ((t : ℝ) ^ m + 1) := by nlinarith
  have hsum : Summable fun t : ℕ => ((t : ℝ) + 1) ^ m * θr ^ t := by
    have hs1 := (summable_pow_mul_geometric_of_norm_lt_one m
      (show ‖θr‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hθr0])).mul_left (2 ^ m)
    have hs2 := (summable_geometric_of_lt_one hθr0 hθr1).mul_left (2 ^ m)
    have hs3 : Summable fun t : ℕ => 2 ^ m * ((t : ℝ) ^ m + 1) * θr ^ t :=
      (hs1.add hs2).congr fun t => by ring
    exact Summable.of_nonneg_of_le (fun t => by positivity)
      (fun t => mul_le_mul_of_nonneg_right (hb t) (pow_nonneg hθr0 t)) hs3
  have heq : ∀ t : ℕ, ((t : ℝ≥0∞) + 1) ^ m * (ENNReal.ofReal (Real.exp w) * θ ^ t)
      = ENNReal.ofReal (Real.exp w * (((t : ℝ) + 1) ^ m * θr ^ t)) := by
    intro t
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow hθr0, hθr,
      ENNReal.ofReal_toReal hθfin, ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    ring
  calc ∫⁻ d, cycLen s S d ^ m ∂P
      ≤ ∫⁻ d, ∑' t : ℕ, ((t : ℝ≥0∞) + 1) ^ m * (E t).indicator 1 d ∂P :=
        lintegral_mono fun d => cycLen_pow_le s S hsS m d
    _ = ∑' t : ℕ, ((t : ℝ≥0∞) + 1) ^ m * P (E t) := by
        rw [lintegral_tsum (f := fun (t : ℕ) d => ((t : ℝ≥0∞) + 1) ^ m * (E t).indicator 1 d)
          fun t => ((measurable_one.indicator (hEm t)).const_mul _).aemeasurable]
        congr 1
        funext t
        rw [lintegral_const_mul _ (measurable_one.indicator (hEm t)),
          lintegral_indicator_one (hEm t)]
    _ ≤ ∑' t : ℕ, ((t : ℝ≥0∞) + 1) ^ m * (ENNReal.ofReal (Real.exp w) * θ ^ t) :=
        ENNReal.tsum_le_tsum fun t => mul_le_mul_of_nonneg_left (hPE t) (by positivity)
    _ = ENNReal.ofReal (∑' t : ℕ, Real.exp w * (((t : ℝ) + 1) ^ m * θr ^ t)) := by
        rw [tsum_congr heq, ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity)
          (hsum.mul_left _)]
    _ < ∞ := ENNReal.ofReal_lt_top

/-! ### The canonical pair -/

/-- With `K > 0`, the value `J` exceeds `min f`, and some cycle that starts at the left end
`a` of `{f < J}` and orders up to `S ∈ (a, b]` costs exactly `J`. -/
lemma canonical_exists (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f)
    (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (K : ℝ) (hKpos : 0 < K) (J : ℝ)
    (hJ0 : 0 ≤ J) (hval : valueFrom ρ f K 0 = ENNReal.ofReal J)
    (hpair : ∀ s S : ℝ, s < S →
      0 ≤ K + ∫ x in Set.Ico 0 (S - s), (f (S - x) - J) ∂(renewalMeasure ρ)) :
    ∃ s S : ℝ, s < S ∧ f s = J ∧ (∀ y ∈ Set.Icc s S, f y ≤ J) ∧
      K + ∫ x in Set.Ico 0 (S - s), (f (S - x) - J) ∂(renewalMeasure ρ) = 0 := by
  have hcont_shift : ∀ y : ℝ, Continuous fun x : ℝ => f (y - x) := fun y =>
    hfc.comp (continuous_const.sub continuous_id)
  -- Step 1: `{f < J}` is nonempty
  have hAne0 : ∃ y, f y < J := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨R, hR⟩ := hfco (J + 1)
    set L : ℝ := 2 * |R| + 1 with hL
    set NL : ℝ := (renewalMeasure ρ (Set.Ico 0 L)).toReal with hNL
    have hNL1 : 1 ≤ NL := one_le_renewal_toReal ρ hρ (by positivity)
    set η : ℝ := min 1 (K / (2 * NL)) with hη
    have hη0 : 0 < η := lt_min one_pos (div_pos hKpos (by linarith))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηK : η * NL ≤ K / 2 := by
      have h : η ≤ K / (2 * NL) := min_le_right _ _
      have hNL0 : NL ≠ 0 := by linarith
      calc η * NL ≤ K / (2 * NL) * NL := mul_le_mul_of_nonneg_right h (by linarith)
        _ = K / 2 := by field_simp
    have hlev := level_le ρ hρ f hfc hfcv hf0 hfco K hKpos.le J hJ0 hval (J + η) (by linarith)
      (fun y h1 h2 => by
        set Ag : Set ℝ := {y | f y < J + η} with hAg
        have hAgne : Ag.Nonempty := by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, Real.sInf_empty] at h1
          rw [hne, Real.sSup_empty] at h2
          linarith
        have hAgR : ∀ z ∈ Ag, -|R| < z ∧ z < |R| := by
          intro z hz
          have hz' : f z < J + η := hz
          have hlt : |z| < R := by
            by_contra hc
            have := hR z (not_lt.1 hc)
            linarith
          have h3 := abs_lt.1 (lt_of_lt_of_le hlt (le_abs_self R))
          exact h3
        have hag : -|R| ≤ sInf Ag := le_csInf hAgne fun z hz => (hAgR z hz).1.le
        have hbg : sSup Ag ≤ |R| := csSup_le hAgne fun z hz => (hAgR z hz).2.le
        have hw : y - sInf Ag ≤ L := by linarith
        have hge : -η * (renewalMeasure ρ (Set.Ico 0 (y - sInf Ag))).toReal
            ≤ ∫ x in Set.Ico 0 (y - sInf Ag), (f (y - x) - (J + η)) ∂(renewalMeasure ρ) :=
          int_ge_const ρ hρ (fun x => f (y - x) - (J + η)) ((hcont_shift y).sub continuous_const)
            (y - sInf Ag) (-η) (fun x _ => by linarith [hcon (y - x)])
        have hmono := renewal_toReal_mono ρ hρ hw
        have hmul := mul_le_mul_of_nonneg_left hmono hη0.le
        linarith)
    linarith
  -- Step 2: the interval `{f < J} = (a, b)`
  obtain ⟨y1, hy1⟩ := hAne0
  set A : Set ℝ := {y | f y < J} with hAdef
  have hy1A : y1 ∈ A := hy1
  obtain ⟨R, hR⟩ := hfco J
  have hAR : ∀ y ∈ A, |y| < R := fun y hy => by
    by_contra h
    exact absurd (hR y (not_lt.1 h)) (not_le.2 hy)
  have hAne : A.Nonempty := ⟨y1, hy1A⟩
  have hAbb : BddBelow A := ⟨-R, fun y hy => by
    have := hAR y hy
    linarith [neg_abs_le y]⟩
  have hAba : BddAbove A := ⟨R, fun y hy => by
    have := hAR y hy
    linarith [le_abs_self y]⟩
  have hAopen : IsOpen A := isOpen_lt hfc continuous_const
  set a := sInf A with ha
  set b := sSup A with hb
  have ha_notin : a ∉ A := by
    intro haA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAopen a haA
    have hmem : a - ε / 2 ∈ A := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
      linarith)
    have := csInf_le hAbb hmem
    linarith
  have hb_notin : b ∉ A := by
    intro hbA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAopen b hbA
    have hmem : b + ε / 2 ∈ A := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith)
    have := le_csSup hAba hmem
    linarith
  have hfa_le : f a ≤ J := closure_lt_subset_le hfc continuous_const (csInf_mem_closure hAne hAbb)
  have hfb_le : f b ≤ J := closure_lt_subset_le hfc continuous_const (csSup_mem_closure hAne hAba)
  have hfa : f a = J := le_antisymm hfa_le (not_lt.1 ha_notin)
  have hfb : f b = J := le_antisymm hfb_le (not_lt.1 hb_notin)
  have hK3 : ∀ y, a < y → y < b → f y < J := by
    intro y h1 h2
    obtain ⟨z1, hz1A, hz1⟩ := exists_lt_of_csInf_lt hAne h1
    obtain ⟨z2, hz2A, hz2⟩ := exists_lt_of_lt_csSup hAne h2
    exact lt_of_le_of_lt (hfcv.le_max_of_mem_Icc (Set.mem_univ z1) (Set.mem_univ z2)
      ⟨hz1.le, hz2.le⟩) (max_lt hz1A hz2A)
  have hab : a < b := by
    have h1 : a ≤ y1 := csInf_le hAbb hy1A
    have h2 : y1 ≤ b := le_csSup hAba hy1A
    have h3 : a ≠ y1 := fun h => ha_notin (h ▸ hy1A)
    exact lt_of_lt_of_le (lt_of_le_of_ne h1 h3) h2
  have hIcc : ∀ y ∈ Set.Icc a b, f y ≤ J := fun y hy =>
    (hfcv.le_max_of_mem_Icc (Set.mem_univ a) (Set.mem_univ b) hy).trans (max_le hfa_le hfb_le)
  set mid := (a + b) / 2 with hmid
  have hfmid : f mid < J := hK3 mid (by linarith) (by linarith)
  have hleft : ∀ z, z < a → J < f z := by
    intro z hz
    have hs := hfcv.slope_mono_adjacent (Set.mem_univ z) (Set.mem_univ mid) hz
      (show a < mid by linarith)
    rw [hfa] at hs
    have h1 : (f mid - J) / (mid - a) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    have h2 : (J - f z) / (a - z) < 0 := lt_of_le_of_lt hs h1
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (div_nonneg (by linarith) (by linarith)))
  have hright : ∀ z, b < z → J < f z := by
    intro z hz
    have hs := hfcv.slope_mono_adjacent (Set.mem_univ mid) (Set.mem_univ z)
      (show mid < b by linarith) hz
    rw [hfb] at hs
    have h1 : 0 < (J - f mid) / (b - mid) := div_pos (by linarith) (by linarith)
    have h2 : 0 < (f z - J) / (z - b) := lt_of_lt_of_le h1 hs
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)))
  have hK1 : ∀ y, y ≤ a → J ≤ f y := fun y hy => by
    rcases eq_or_lt_of_le hy with h | h
    · rw [h, hfa]
    · exact (hleft y h).le
  -- Step 3: the relative cost `G(y) = ∫_{[0,y-a)} (f(y-x) - J) U(dx)` is continuous
  set h : ℝ → ℝ := fun z => if z ≤ a then 0 else f z - J with hh
  have hhc : Continuous h := by
    have := continuous_if_le (f := fun z : ℝ => z) (g := fun _ => a) (f' := fun _ => (0 : ℝ))
      (g' := fun z => f z - J) continuous_id continuous_const continuousOn_const
      (hfc.sub continuous_const).continuousOn (fun z hz => by
        rw [hz, hfa, sub_self])
    exact this
  have hhs : ∀ y : ℝ, Continuous fun x : ℝ => h (y - x) := fun y =>
    hhc.comp (continuous_const.sub continuous_id)
  set G : ℝ → ℝ := fun y => ∫ x in Set.Ici 0, h (y - x) ∂(renewalMeasure ρ) with hG
  have hGw : ∀ y w, y - a ≤ w → ∫ x in Set.Ico 0 w, h (y - x) ∂(renewalMeasure ρ) = G y := by
    intro y w hw
    simp only [hG]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      Set.Ico_subset_Ici_self]
    intro x hx
    have h1 : w ≤ x := by
      rcases hx with ⟨hx1, hx2⟩
      simp only [Set.mem_Ici] at hx1
      simp only [Set.mem_Ico, not_and, not_lt] at hx2
      exact hx2 hx1
    simp only [hh, if_pos (show y - x ≤ a by linarith)]
  have hGf : ∀ y, G y = ∫ x in Set.Ico 0 (y - a), (f (y - x) - J) ∂(renewalMeasure ρ) := by
    intro y
    rw [← hGw y (y - a) le_rfl]
    refine setIntegral_congr_fun measurableSet_Ico fun x hx => ?_
    simp only [hh, if_neg (show ¬ (y - x ≤ a) by linarith [hx.2])]
  have hGc : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro y₀
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a - 2) (b := y₀ + 1)).exists_bound_of_continuousOn
      hhc.continuousOn
    show ContinuousAt (fun y => ∫ x, h (y - x) ∂((renewalMeasure ρ).restrict (Set.Ici 0))) y₀
    refine continuousAt_of_dominated (bound := (Set.Iio (y₀ + 1 - a)).indicator fun _ => C)
      ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun y => (hhs y).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
      refine ae_restrict_of_forall_mem measurableSet_Ici fun x hx => ?_
      simp only [Set.mem_Ici] at hx
      by_cases hxw : x < y₀ + 1 - a
      · rw [Set.indicator_of_mem (show x ∈ Set.Iio (y₀ + 1 - a) from hxw)]
        exact hC (y - x) ⟨by linarith, by linarith⟩
      · rw [Set.indicator_of_notMem (show x ∉ Set.Iio (y₀ + 1 - a) from hxw)]
        have : y - x ≤ a := by
          have : y₀ + 1 - a ≤ x := not_lt.1 hxw
          linarith
        simp [hh, this]
    · refine (integrableOn_const ?_).integrable_indicator measurableSet_Iio
      rw [Measure.restrict_apply measurableSet_Iio, Set.Iio_inter_Ici]
      exact (renewalMeasure_Ico_lt_top ρ hρ _).ne
    · exact ae_of_all _ fun x => (hhc.comp (continuous_id.sub continuous_const)).continuousAt
  have hΦc : Continuous fun y => K + G y := continuous_const.add hGc
  have hGa : ∀ y, y ≤ a → G y = 0 := fun y hy => by
    rw [← hGw y 0 (by linarith)]
    simp
  have hGnn : ∀ y, a < y → -K ≤ G y := fun y hy => by
    have := hpair a y hy
    rw [hGf]
    linarith
  -- Step 4: `K + G` vanishes somewhere on `(a, b]`
  obtain ⟨S, hS1, hS2, hS0⟩ : ∃ S, a < S ∧ S ≤ b ∧ K + G S = 0 := by
    by_contra hcon
    push_neg at hcon
    have hpos : ∀ y ∈ Set.Icc a b, 0 < K + G y := fun y hy => by
      rcases eq_or_lt_of_le hy.1 with h' | h'
      · rw [← h', hGa a le_rfl]
        linarith
      · exact lt_of_le_of_ne (by linarith [hGnn y h']) (hcon y h' hy.2).symm
    obtain ⟨ym, hym, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
      ⟨a, le_rfl, hab.le⟩ hΦc.continuousOn
    set m := K + G ym with hm
    have hm0 : 0 < m := hpos ym hym
    have hmle : ∀ y ∈ Set.Icc a b, m ≤ K + G y := fun y hy => hmin hy
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.1 (hΦc.continuousAt (x := b)) (m / 2)
      (by linarith)
    set ε := δ / 2 with hε
    have hε0 : 0 < ε := by linarith
    have hext : ∀ y, y ≤ b + ε → m / 2 ≤ K + G y := by
      intro y hy
      rcases le_or_gt y a with h1 | h1
      · rw [hGa y h1]
        have := hmle a ⟨le_rfl, hab.le⟩
        rw [hGa a le_rfl] at this
        linarith
      rcases le_or_gt y b with h2 | h2
      · linarith [hmle y ⟨h1.le, h2⟩]
      · have hd : dist y b < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith
        have h3 := hδ hd
        rw [Real.dist_eq] at h3
        have h4 := hmle b ⟨hab.le, le_rfl⟩
        linarith [(abs_lt.1 h3).1]
    have hfl : J < f (a - 1) := hleft (a - 1) (by linarith)
    have hfr : J < f (b + ε) := hright (b + ε) (by linarith)
    set L : ℝ := b + ε - (a - 1) with hL
    set NL : ℝ := (renewalMeasure ρ (Set.Ico 0 L)).toReal with hNL
    have hNL1 : 1 ≤ NL := one_le_renewal_toReal ρ hρ (by linarith)
    set η : ℝ := min (min ((f (a - 1) - J) / 2) ((f (b + ε) - J) / 2)) (m / (2 * NL)) with hη
    have hη0 : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (div_pos hm0 (by linarith))
    have hη1 : η ≤ (f (a - 1) - J) / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hη2 : η ≤ (f (b + ε) - J) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hη3 : η ≤ m / (2 * NL) := min_le_right _ _
    have hηN : η * NL ≤ m / 2 := by
      have hNL0 : NL ≠ 0 := by linarith
      calc η * NL ≤ m / (2 * NL) * NL := mul_le_mul_of_nonneg_right hη3 (by linarith)
        _ = m / 2 := by field_simp
    have hlmono : ∀ z, z ≤ a - 1 → f (a - 1) ≤ f z := fun z hz => by
      have := hfcv.le_max_of_mem_Icc (Set.mem_univ z) (Set.mem_univ mid) ⟨hz, by linarith⟩
      rcases le_max_iff.1 this with h' | h'
      · exact h'
      · linarith
    have hrmono : ∀ z, b + ε ≤ z → f (b + ε) ≤ f z := fun z hz => by
      have := hfcv.le_max_of_mem_Icc (Set.mem_univ mid) (Set.mem_univ z) ⟨by linarith, hz⟩
      rcases le_max_iff.1 this with h' | h'
      · linarith
      · exact h'
    have hlev := level_le ρ hρ f hfc hfcv hf0 hfco K hKpos.le J hJ0 hval (J + η) (by linarith)
      (fun y h1 h2 => by
        set Ag : Set ℝ := {y | f y < J + η} with hAg
        have hAAg : A ⊆ Ag := fun z hz => by
          have hz' : f z < J := hz
          show f z < J + η
          linarith
        have hAgne : Ag.Nonempty := hAne.mono hAAg
        have hAgb : ∀ z ∈ Ag, a - 1 < z ∧ z < b + ε := by
          intro z hz
          have hz' : f z < J + η := hz
          constructor
          · by_contra hc
            push_neg at hc
            linarith [hlmono z hc]
          · by_contra hc
            push_neg at hc
            linarith [hrmono z hc]
        have hAgbb : BddBelow Ag := ⟨a - 1, fun z hz => (hAgb z hz).1.le⟩
        have hag1 : a - 1 ≤ sInf Ag := le_csInf hAgne fun z hz => (hAgb z hz).1.le
        have hag2 : sInf Ag ≤ a := csInf_le_csInf hAgbb hAne hAAg
        have hyAg : y ∈ Ag := by
          obtain ⟨z1, hz1, hz1y⟩ := exists_lt_of_csInf_lt hAgne h1
          obtain ⟨z2, hz2, hz2y⟩ := exists_lt_of_lt_csSup hAgne h2
          have := hfcv.le_max_of_mem_Icc (Set.mem_univ z1) (Set.mem_univ z2) ⟨hz1y.le, hz2y.le⟩
          have hz1' : f z1 < J + η := hz1
          have hz2' : f z2 < J + η := hz2
          show f y < J + η
          exact lt_of_le_of_lt this (max_lt hz1' hz2')
        have hy := hAgb y hyAg
        have hcmp : ∫ x in Set.Ico 0 (y - sInf Ag), (h (y - x) - η) ∂(renewalMeasure ρ)
            ≤ ∫ x in Set.Ico 0 (y - sInf Ag), (f (y - x) - (J + η)) ∂(renewalMeasure ρ) :=
          setIntegral_mono_on (intOn_Ico ρ hρ _ ((hhs y).sub continuous_const) _)
            (intOn_Ico ρ hρ _ ((hcont_shift y).sub continuous_const) _) measurableSet_Ico
            (fun x _ => by
              simp only [hh]
              split_ifs with hx
              · linarith [hK1 (y - x) hx]
              · linarith)
        have hsplit : ∫ x in Set.Ico 0 (y - sInf Ag), (h (y - x) - η) ∂(renewalMeasure ρ)
            = G y - η * (renewalMeasure ρ (Set.Ico 0 (y - sInf Ag))).toReal := by
          rw [int_sub_const ρ hρ (fun x => h (y - x)) (hhs y), hGw y _ (by linarith)]
        have hNm := renewal_toReal_mono ρ hρ (show y - sInf Ag ≤ L by linarith)
        have hmul := mul_le_mul_of_nonneg_left hNm hη0.le
        have hK' := hext y hy.2.le
        linarith)
    linarith
  refine ⟨a, S, hS1, hfa, fun y hy => hIcc y ⟨hy.1, hy.2.trans hS2⟩, ?_⟩
  rw [← hGf S]
  exact hS0

end SLL

open SLL in
theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ0 : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (hρ1 : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞)
    (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y) (hfcv : ConvexOn ℝ Set.univ f)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (hfL : ∃ L : ℝ≥0, LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ J : ℝ, 0 ≤ J ∧ slValue ρ f K = ENNReal.ofReal J ∧
      (∀ y0 : ℝ, (⨅ (U : Type) (_ : MeasurableSpace U) (ν : Measure U)
          (_ : IsProbabilityMeasure ν) (q : SLPolicy U) (_ : SLAdmissible q),
            slAvgCost ρ f K y0 q ν) = slValue ρ f K) ∧
      (∀ s S : ℝ, s ≤ S → ssAvgCost ρ f K s S = slValue ρ f K → ∀ y0 : ℝ,
        ∃ q : SLPolicy Unit, SLAdmissible q ∧
          (∀ (t : ℕ) (d : ℕ → ℝ≥0), q t () d = if slPos y0 q () d t - q t () d ≤ s
            then S - (slPos y0 q () d t - q t () d) else 0) ∧
          slAvgCost ρ f K y0 q (Measure.dirac ()) = slValue ρ f K) ∧
      (0 < K → ∃ s S : ℝ, IsCanonicalOptimum ρ f K s S ∧
        (∀ (d : ℕ → ℝ≥0) (t : ℕ), s < ssPost s S d t ∧ ssPost s S d t ≤ S) ∧
        ∀ m : ℕ, ∫⁻ d, (⨅ (t : ℕ) (_ : 1 ≤ t ∧ ssPre s S d t ≤ s), (t : ℝ≥0∞)) ^ m
          ∂(Measure.infinitePi fun _ : ℕ => ρ) < ∞) ∧
      (K = 0 → ∃ x : ℝ, (∀ y, f x ≤ f y) ∧ J = f x ∧ ssAvgCost ρ f K x x = slValue ρ f K) ∧
      (∃ u : ℝ → ℝ, Measurable u ∧ (∀ y z, u y - u z ≤ K) ∧ (K = 0 → ∀ y, u y = 0) ∧
        ∀ y, J + max (f y - J) 0 ≤ f y + ∫ d, u (y - (d : ℝ)) ∂ρ - u y) ∧
      (∀ {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]
        (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [IsProbabilityMeasure ν]
        (g : α → ℝ≥0), Measurable g → μ.map g = ρ →
        ∀ q : ℕ → U → (ℕ → α) → ℝ,
          (∀ (t : ℕ) (u : U) (d d' : ℕ → α), (∀ r < t, d r = d' r) → q t u d = q t u d') →
          (∀ t, Measurable fun ω : U × (ℕ → α) => q t ω.1 ω.2) → (∀ t u d, 0 ≤ q t u d) →
          ∀ (y0 : ℝ) (T : ℕ), 1 ≤ T →
            ENNReal.ofReal (T * J - K) ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
              (K * (if 0 < q t ω.1 (padHist T ω.2) then 1 else 0)
                + f (y0 + ∑ s ∈ Finset.range (t + 1), q s ω.1 (padHist T ω.2)
                  - ∑ s ∈ Finset.range t, (g (padHist T ω.2 s) : ℝ)))
              ∂(ν.prod (Measure.pi fun _ : Fin T => μ))) := by
  obtain ⟨Lf, hLf⟩ := hfL
  have hfc : Continuous f := hLf.continuous
  have hfm : Measurable f := hfc.measurable
  have hbdd : ∀ s S : ℝ, ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C := fun s S => by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := S)).exists_bound_of_continuousOn
      hfc.continuousOn
    exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩
  have hRR : ∀ s S : ℝ, s < S → ssAvgCost ρ f K s S
      = ENNReal.ofReal ((K + ∫ x in Set.Ico 0 (S - s), f (S - x) ∂(renewalMeasure ρ))
          / (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal) := fun s S h =>
    ss_renewal_reward ρ hρ0 f hfm hf0 K s S hK h (hbdd s S)
  have hshift : ∀ y : ℝ, Continuous fun x : ℝ => f (y - x) := fun y =>
    hfc.comp (continuous_const.sub continuous_id)
  -- the cheapest `(s,S)` cost
  set J' : ℝ≥0∞ := ⨅ p : {p : ℝ × ℝ // p.1 < p.2}, ssAvgCost ρ f K p.1.1 p.1.2 with hJ'
  have hJ'fin : J' ≠ ∞ := by
    have h1 : J' ≤ ssAvgCost ρ f K 0 1 :=
      iInf_le (fun p : {p : ℝ × ℝ // p.1 < p.2} => ssAvgCost ρ f K p.1.1 p.1.2)
        ⟨(0, 1), by norm_num⟩
    rw [hRR 0 1 (by norm_num)] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  set J : ℝ := J'.toReal with hJdef
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hJ'eq : J' = ENNReal.ofReal J := (ENNReal.ofReal_toReal hJ'fin).symm
  have hpair : ∀ s S : ℝ, s < S →
      0 ≤ K + ∫ x in Set.Ico 0 (S - s), (f (S - x) - J) ∂(renewalMeasure ρ) := by
    intro s S hsS
    have h1 : J' ≤ ssAvgCost ρ f K s S :=
      iInf_le (fun p : {p : ℝ × ℝ // p.1 < p.2} => ssAvgCost ρ f K p.1.1 p.1.2) ⟨(s, S), hsS⟩
    rw [hJ'eq, hRR s S hsS] at h1
    have hN : 0 < (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal :=
      lt_of_lt_of_le one_pos (one_le_renewal_toReal ρ hρ0 (by linarith))
    have hnum : 0 ≤ K + ∫ x in Set.Ico 0 (S - s), f (S - x) ∂(renewalMeasure ρ) :=
      add_nonneg hK (setIntegral_nonneg measurableSet_Ico fun x _ => hf0 _)
    rw [ENNReal.ofReal_le_ofReal_iff (div_nonneg hnum hN.le), le_div_iff₀ hN] at h1
    rw [int_sub_const ρ hρ0 (fun x => f (S - x)) (hshift S)]
    linarith
  -- the value from every starting position is `J`
  have hVle : ∀ y0, valueFrom ρ f K y0 ≤ ENNReal.ofReal J := fun y0 => by
    rw [← hJ'eq]
    exact le_iInf fun p => value_le_ss ρ hρ0 f hfc hf0 K y0 p.1.1 p.1.2 hK p.2.le
  obtain ⟨v, hvm, hvb, hsub⟩ := level_subsolution ρ hρ0 f hfc hfcv hf0 hfco K hK J hJ0
    (fun y h1 _ => by
      have := hpair _ y h1
      rw [int_sub_const ρ hρ0 (fun x => f (y - x)) (hshift y)] at this
      linarith)
  have hsub' : ∀ y, J ≤ f y + ∫ d, v (y - (d : ℝ)) ∂ρ - v y := fun y =>
    le_trans (le_add_of_nonneg_right (le_max_right _ _)) (hsub y)
  have hVeq : ∀ y0, valueFrom ρ f K y0 = ENNReal.ofReal J := fun y0 =>
    le_antisymm (hVle y0) (value_ge_of_sub ρ f hfm hf0 K J v hvm hvb hsub' y0)
  have hval : slValue ρ f K = ENNReal.ofReal J := hVeq 0
  refine ⟨J, hJ0, hval, fun y0 => (hVeq y0).trans hval.symm, ?_, ?_, ?_,
    ⟨v, hvm, fun y z => by linarith [(hvb y).2, (hvb z).1],
      fun hK0 y => by linarith [(hvb y).1, (hvb y).2], hsub⟩, ?_⟩
  · -- an `(s,S)` pair that is optimal from `S` is optimal from every starting position
    intro s S hsS hopt y0
    refine ⟨rulePolicy y0 s S, rulePolicy_adm y0 s S hsS, fun t d => ?_, ?_⟩
    · have h1 := slPos_rulePolicy y0 s S d t
      have h2 : slPos y0 (rulePolicy y0 s S) () d t - rulePolicy y0 s S t () d
          = rulePre y0 s S d t := by
        rw [h1]
        simp only [rulePolicy]
        split_ifs <;> ring
      rw [h2]
      rfl
    · refine le_antisymm ?_ ?_
      · rw [← hopt]
        exact slAvg_rule_le ρ hρ0 f hfc hf0 K y0 s S hK hsS
      · rw [hval, ← hVeq y0]
        exact valueFrom_le ρ f K y0 _ _ (rulePolicy_adm y0 s S hsS)
  · -- `K > 0`: a canonical optimal pair
    intro hKpos
    obtain ⟨s, S, hsS, hfs, hle, hzero⟩ :=
      canonical_exists ρ hρ0 f hfc hfcv hf0 hfco K hKpos J hJ0 (hVeq 0) hpair
    have hN : 0 < (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal :=
      lt_of_lt_of_le one_pos (one_le_renewal_toReal ρ hρ0 (by linarith))
    have hcost : ssAvgCost ρ f K s S = slValue ρ f K := by
      rw [hRR s S hsS, hval]
      congr 1
      rw [int_sub_const ρ hρ0 (fun x => f (S - x)) (hshift S)] at hzero
      have hN' := hN.ne'
      field_simp
      linarith
    refine ⟨s, S, ⟨hsS, hcost, by rw [hfs, hval], ?_, ?_⟩, fun d t => ssPost_mem s S hsS d t,
      fun m => cycLen_moment ρ hρ0 s S hsS m⟩
    · rw [hval]
      exact ENNReal.ofReal_le_ofReal (hle S ⟨hsS.le, le_rfl⟩)
    · intro y hy
      rw [hval]
      exact ENNReal.ofReal_le_ofReal (hle y hy)
  · -- `K = 0`: base stock at a minimizer
    intro hK0
    obtain ⟨x, hx⟩ : ∃ x, ∀ y, f x ≤ f y := by
      obtain ⟨R, hR⟩ := hfco (f 0)
      obtain ⟨x, hxI, hxmin⟩ := (isCompact_Icc (a := -|R|) (b := |R|)).exists_isMinOn
        ⟨0, by simp [abs_nonneg]⟩ hfc.continuousOn
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
        have h0 : f x ≤ f 0 := hxmin ⟨by simp [abs_nonneg], by simp [abs_nonneg]⟩
        exact h0.trans (hR y h1)
    have hSS : ssAvgCost ρ f K x x = ENNReal.ofReal (f x) := by
      rw [ss_avg_SS ρ f hf0 K x hK, hK0, zero_mul, add_zero]
    have hle : ENNReal.ofReal J ≤ ENNReal.ofReal (f x) := by
      rw [← hVeq 0, ← hSS]
      exact value_le_ss ρ hρ0 f hfc hf0 K 0 x x hK le_rfl
    have hge : ENNReal.ofReal (f x) ≤ ENNReal.ofReal J := by
      rw [← hVeq 0]
      exact value_ge_of_sub ρ f hfm hf0 K (f x) (fun _ => 0) measurable_const
        (fun y => ⟨by linarith, le_rfl⟩) (fun y => by simp [hx y]) 0
    have hJx : J = f x := (ENNReal.ofReal_eq_ofReal_iff hJ0 (hf0 x)).1 (le_antisymm hle hge)
    exact ⟨x, hx, hJx, by rw [hSS, hval, hJx]⟩
  · -- the finite-horizon bound, for policies that use network history and randomization
    intro α Uα _ _ _ μ _ ν _ g hg hμg q hna hqm hq0 y0 T hT
    have hsubμ : ∀ y, J ≤ f y + ∫ a, v (y - (g a : ℝ)) ∂μ - v y := by
      intro y
      have h := hsub' y
      have hint : ∫ d, v (y - (d : ℝ)) ∂ρ = ∫ a, v (y - (g a : ℝ)) ∂μ := by
        rw [← hμg, integral_map hg.aemeasurable]
        exact (hvm.comp (measurable_const.sub measurable_coe_nnreal_real)).aestronglyMeasurable
      rwa [hint] at h
    have hb := sl_adapted_bound μ ν g hg q hna hqm hq0 y0 f hfm hf0 K J v hvm hvb hsubμ T T le_rfl
    rw [ENNReal.ofReal_sub _ hK]
    exact tsub_le_iff_right.2 hb
