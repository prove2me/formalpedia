-- Prove2me | solution 1 for SelfishMiningRuin.ValueFn.Vhat_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:44:56.823427+00:00
-- url     : https://prove2.me/submissions/26422937-660c-4c4a-9ef0-8392724a655c

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model

set_option autoImplicit false

namespace SMRLin

open MeasureTheory ProbabilityTheory SelfishMiningRuin.ValueFn Set
open scoped ENNReal

lemma expM_Iic {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Iic x) = ENNReal.ofReal (1 - Real.exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hx]

lemma expM_Iio0 {r : ℝ} (hr : 0 < r) : expMeasure r (Iio 0) = 0 := by
  apply nonpos_iff_eq_zero.mp
  calc expMeasure r (Iio 0) ≤ expMeasure r (Iic 0) := measure_mono Iio_subset_Iic_self
    _ = 0 := by rw [expM_Iic hr le_rfl]; simp

lemma expM_ae_nonneg {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this, expM_Iio0 hr]

lemma expM_single {r x : ℝ} : expMeasure r {x} = 0 := by
  unfold expMeasure gammaMeasure
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

lemma expM_Ioi {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, expM_Iic hr hx]
  have h2 : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

lemma expM_Ici {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Ici x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  rw [← expM_Ioi hr hx]
  apply le_antisymm
  · rw [← Ioi_insert, insert_eq]
    calc expMeasure r ({x} ∪ Ioi x) ≤ expMeasure r {x} + expMeasure r (Ioi x) :=
          measure_union_le _ _
      _ = expMeasure r (Ioi x) := by rw [expM_single, zero_add]
  · exact measure_mono Ioi_subset_Ici_self

lemma expM_Iio {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Iio x) = ENNReal.ofReal (1 - Real.exp (-(r * x))) := by
  rw [← expM_Iic hr hx]
  apply le_antisymm (measure_mono Iio_subset_Iic_self)
  rw [← Iio_insert, insert_eq]
  calc expMeasure r ({x} ∪ Iio x) ≤ expMeasure r {x} + expMeasure r (Iio x) :=
        measure_union_le _ _
    _ = expMeasure r (Iio x) := by rw [expM_single, zero_add]

lemma expM_mean {r : ℝ} (hr : 0 < r) :
    ∫⁻ s, ENNReal.ofReal s ∂(expMeasure r) = ENNReal.ofReal (1 / r) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [lintegral_eq_lintegral_meas_lt _ (expM_ae_nonneg hr) measurable_id.aemeasurable]
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (g := fun x => ENNReal.ofReal (Real.exp (-r * x))) (fun x hx => by
      show expMeasure r (Ioi x) = _
      rw [expM_Ioi hr (le_of_lt hx)]; simp only [neg_mul])]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (by linarith) 0)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  rw [integral_exp_mul_Ioi (by linarith) 0]
  congr 1
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma bern_univ {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : bern r univ = 1 := by
  simp only [bern, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma law_W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam p q : ℝ}
    {W : ℕ → Ω → ℝ} {ξ ζ : ℕ → Ω → Bool}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ) (k : ℕ) : HasLaw (W k) (expMeasure lam) P := by
  have h := hprim.law k
  have hfst : HasLaw (Prod.fst : ℝ × Bool × Bool → ℝ) (expMeasure lam)
      ((expMeasure lam).prod ((bern p).prod (bern q))) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod]
    have : ((bern p).prod (bern q)) univ = 1 := by
      rw [← univ_prod_univ, Measure.prod_prod, bern_univ hp0 hp1, bern_univ hq0 hq1, one_mul]
    rw [this, one_smul]
  exact hfst.comp h

lemma reward_le (z : St) (x y : Bool) : (reward z x y : ℝ) ≤ 2 := by
  cases z <;> cases x <;> cases y <;> simp [reward]

lemma arrival_ge {Ω : Type*} (W : ℕ → Ω → ℝ) (ω : Ω) (hW : ∀ k, 0 ≤ W k ω) (n : ℕ)
    (hn : 1 ≤ n) : W 0 ω ≤ arrival W n ω := by
  unfold arrival
  exact Finset.single_le_sum (f := fun k => W k ω) (fun k _ => hW k)
    (Finset.mem_range.mpr (by omega))

lemma arrival_nonneg {Ω : Type*} (W : ℕ → Ω → ℝ) (ω : Ω) (hW : ∀ k, 0 ≤ W k ω) (n : ℕ) :
    0 ≤ arrival W n ω := Finset.sum_nonneg (fun k _ => hW k)

lemma blocks_zero {Ω : Type*} (W : ℕ → Ω → ℝ) (ω : Ω) (hW : ∀ k, 0 ≤ W k ω) (x : ℝ)
    (hx : x < W 0 ω) : blocks W x ω = 0 := by
  unfold blocks
  have : {n : ℕ | 1 ≤ n ∧ arrival W n ω ≤ x} = ∅ := by
    ext n
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hn
    exact lt_of_lt_of_le hx (arrival_ge W ω hW n hn)
  rw [this, ncard_empty]

lemma pw {Ω : Type*} (W : ℕ → Ω → ℝ) (ξ ζ : ℕ → Ω → Bool) (c b u s : ℝ) (z : St) (ω : Ω)
    (hc : 0 < c) (hb : 0 ≤ b) (hu : 0 ≤ u) (hs : 0 ≤ s) (hW : ∀ k, 0 ≤ W k ω) :
    |(if ENNReal.ofReal s < ruinTime W ξ ζ c b u z ω then surplus W ξ ζ c b u s z ω else 0)|
      ≤ u + (if W 0 ω ≤ u / c then c * s + 2 * b * (blocks W s ω : ℝ) else 0) := by
  have hR : ∀ y, 0 ≤ ∑ k ∈ Finset.range (blocks W y ω),
      (reward (chain ξ ζ z ω k) (ξ k ω) (ζ k ω) : ℝ) ∧
      ∑ k ∈ Finset.range (blocks W y ω), (reward (chain ξ ζ z ω k) (ξ k ω) (ζ k ω) : ℝ)
        ≤ 2 * (blocks W y ω : ℝ) := by
    intro y
    refine ⟨Finset.sum_nonneg (fun k _ => by positivity), ?_⟩
    calc _ ≤ ∑ k ∈ Finset.range (blocks W y ω), (2 : ℝ) :=
          Finset.sum_le_sum (fun k _ => reward_le _ _ _)
      _ = 2 * (blocks W y ω : ℝ) := by simp [mul_comm]
  split_ifs with hT hB hB
  · -- before ruin, a block before u/c
    obtain ⟨r0, r1⟩ := hR s
    unfold surplus
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  · -- before ruin, no block before u/c
    push Not at hB
    have hb0 : blocks W (u / c) ω = 0 := blocks_zero W ω hW _ hB
    have hsur : surplus W ξ ζ c b u (u / c) z ω = 0 := by
      unfold surplus
      rw [hb0]
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      field_simp
      ring
    have hTle : ruinTime W ξ ζ c b u z ω ≤ ENNReal.ofReal (u / c) := by
      apply sInf_le
      exact ⟨u / c, by positivity, hsur, rfl⟩
    have hsl : s < u / c := by
      have := lt_of_lt_of_le hT hTle
      exact (ENNReal.ofReal_lt_ofReal_iff'.mp this).1
    have hbs : blocks W s ω = 0 := blocks_zero W ω hW _ (lt_trans hsl hB)
    unfold surplus
    rw [hbs]
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    have : c * s < u := by
      have := (lt_div_iff₀ hc).mp hsl
      linarith
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [abs_zero]
    have := (hR s).1
    positivity
  · simp only [abs_zero, add_zero]
    exact hu

lemma lintegral_prod_indep₀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ≥0∞) (hX : iIndepFun X P)
    (hm : ∀ i, AEMeasurable (X i) P) (s : Finset ℕ) :
    ∫⁻ ω, ∏ i ∈ s, X i ω ∂P = ∏ i ∈ s, ∫⁻ ω, X i ω ∂P := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | cons j s hj ihs =>
    simp only [← Finset.prod_apply, Finset.prod_cons, ← ihs]
    apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    · exact hm j
    · exact s.aemeasurable_prod (fun i _ ↦ hm i)
    · exact (iIndepFun.indepFun_finsetProd_of_notMem₀ hX hm hj).symm

/-- `blocks` is dominated by the counting series. -/
lemma blocks_le_N {Ω : Type*} (W : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) :
    (blocks W s ω : ℝ≥0∞) ≤ ∑' n : ℕ,
      (if 1 ≤ n then (Ici (arrival W n ω)).indicator (fun _ => (1 : ℝ≥0∞)) s else 0) := by
  unfold blocks
  by_cases hfin : {n : ℕ | 1 ≤ n ∧ arrival W n ω ≤ s}.Finite
  · rw [Set.ncard_eq_toFinset_card _ hfin]
    calc ((hfin.toFinset.card : ℕ) : ℝ≥0∞)
        = ∑ n ∈ hfin.toFinset,
          (if 1 ≤ n then (Ici (arrival W n ω)).indicator (fun _ => (1 : ℝ≥0∞)) s else 0) := by
          rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
          · simp
          · intro n hn
            simp only [Finite.mem_toFinset, mem_ofPred_eq] at hn
            rw [if_pos hn.1, indicator_of_mem (by simpa using hn.2)]
      _ ≤ _ := ENNReal.sum_le_tsum _
  · rw [Set.Infinite.ncard hfin]
    simp

end SMRLin

open MeasureTheory ProbabilityTheory SelfishMiningRuin.ValueFn Set SMRLin
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ) :
    ∃ K : ℝ, ∀ z : St, ∀ u : ℝ, 0 ≤ u → |Vhat P W ξ ζ c b u t z| ≤ K * u := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hμS := isProbabilityMeasure_expMeasure hti
  have hlawW := law_W hp0.le hp1.le hq0 hq1 hprim
  have hWae : ∀ k, AEMeasurable (W k) P := fun k => (hlawW k).aemeasurable
  have hgood : ∀ᵐ ω ∂P, ∀ k, 0 ≤ W k ω := by
    rw [ae_all_iff]
    intro k
    exact ((hlawW k).ae_iff (p := fun x => 0 ≤ x) (measurableSet_Ici.mem)).mpr
      (expM_ae_nonneg hlam)
  -- the ratio ρ0 < 1
  set ρr : ℝ := 1 - Real.exp (-lam) * (1 - Real.exp (-t⁻¹)) with hρr
  have hel : 0 < Real.exp (-lam) := Real.exp_pos _
  have hel1 : Real.exp (-lam) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have het : 0 < Real.exp (-t⁻¹) := Real.exp_pos _
  have het1 : Real.exp (-t⁻¹) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hρr0 : 0 ≤ ρr := by nlinarith
  have hρr1 : ρr < 1 := by nlinarith
  have hρ : ∫⁻ x, ENNReal.ofReal (Real.exp (-(t⁻¹ * x))) ∂(expMeasure lam) ≤ ENNReal.ofReal ρr := by
    rw [← lintegral_add_compl _ (measurableSet_Ici (a := (1:ℝ)))]
    have h1 : ∫⁻ x in Ici 1, ENNReal.ofReal (Real.exp (-(t⁻¹ * x))) ∂(expMeasure lam)
        ≤ ENNReal.ofReal (Real.exp (-t⁻¹)) * ENNReal.ofReal (Real.exp (-lam)) := by
      calc _ ≤ ∫⁻ x in Ici 1, ENNReal.ofReal (Real.exp (-t⁻¹)) ∂(expMeasure lam) := by
            apply setLIntegral_mono measurable_const
            intro x hx
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp.mpr
            have : (1:ℝ) ≤ x := hx
            nlinarith
        _ = _ := by
            rw [setLIntegral_const, expM_Ici hlam zero_le_one, mul_one]
    have h2 : ∫⁻ x in (Ici 1)ᶜ, ENNReal.ofReal (Real.exp (-(t⁻¹ * x))) ∂(expMeasure lam)
        ≤ ENNReal.ofReal (1 - Real.exp (-lam)) := by
      calc _ ≤ ∫⁻ x in (Ici 1)ᶜ, 1 ∂(expMeasure lam) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_of_ae (expM_ae_nonneg hlam)] with x hx
            rw [← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_one_iff.mpr
            nlinarith
        _ = _ := by
            rw [setLIntegral_const, compl_Ici, expM_Iio hlam zero_le_one, one_mul, mul_one]
    calc _ ≤ ENNReal.ofReal (Real.exp (-t⁻¹)) * ENNReal.ofReal (Real.exp (-lam)) +
          ENNReal.ofReal (1 - Real.exp (-lam)) := add_le_add h1 h2
      _ = ENNReal.ofReal ρr := by
          rw [← ENNReal.ofReal_mul het.le, ← ENNReal.ofReal_add (by positivity) (by linarith)]
          congr 1
          rw [hρr]; ring
  -- the constant
  refine ⟨1 + lam * t + 2 * b * (lam / c) * (1 - ρr)⁻¹, ?_⟩
  intro z u hu
  set μS := expMeasure t⁻¹ with hμSdef
  set ind : Ω → ℝ≥0∞ := fun ω => (Iic (u / c)).indicator (fun _ => (1 : ℝ≥0∞)) (W 0 ω)
    with hind
  set N : ℝ → Ω → ℝ≥0∞ := fun s ω => ∑' n : ℕ,
      (if 1 ≤ n then (Ici (arrival W n ω)).indicator (fun _ => (1 : ℝ≥0∞)) s else 0) with hN
  set Y : ℝ → Ω → ℝ≥0∞ := fun s ω =>
    ENNReal.ofReal u + ind ω * ENNReal.ofReal (c * s) + ind ω * (ENNReal.ofReal (2 * b) * N s ω)
    with hY
  have hindm : AEMeasurable ind P :=
    (measurable_const.indicator measurableSet_Iic).comp_aemeasurable (hWae 0)
  have hPB : ∫⁻ ω, ind ω ∂P ≤ ENNReal.ofReal (lam * (u / c)) := by
    rw [hind, (hlawW 0).lintegral_comp (f := (Iic (u / c)).indicator (fun _ => (1 : ℝ≥0∞)))
      ((measurable_const.indicator measurableSet_Iic).aemeasurable),
      lintegral_indicator_const measurableSet_Iic, one_mul, expM_Iic hlam (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := Real.add_one_le_exp (-(lam * (u / c)))
    linarith
  -- pointwise bound
  have hpt : ∀ s, 0 ≤ s → ∀ ω, (∀ k, 0 ≤ W k ω) →
      ENNReal.ofReal ‖(if ENNReal.ofReal s < ruinTime W ξ ζ c b u z ω
        then surplus W ξ ζ c b u s z ω else 0)‖ ≤ Y s ω := by
    intro s hs ω hW
    have h := pw W ξ ζ c b u s z ω hc hb.le hu hs hW
    rw [Real.norm_eq_abs]
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    simp only [hY, hind]
    by_cases hB : W 0 ω ≤ u / c
    · rw [if_pos hB, indicator_of_mem (show W 0 ω ∈ Iic (u / c) from hB), one_mul, one_mul]
      rw [ENNReal.ofReal_add hu (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
        add_assoc]
      gcongr
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      gcongr
      exact blocks_le_N W s ω
    · rw [if_neg hB, add_zero]
      exact le_trans le_self_add le_self_add
  have harr : ∀ n, AEMeasurable (arrival W n) P := by
    intro n
    unfold arrival
    exact Finset.aemeasurable_fun_sum _ (fun k _ => hWae k)
  -- step i: inner integral
  set PB := ∫⁻ ω, ind ω ∂P with hPBdef
  set G : ℝ → ℝ≥0∞ := fun s => ∫⁻ ω, ind ω * (ENNReal.ofReal (2 * b) * N s ω) ∂P with hG
  have hinner : ∀ s, ∫⁻ ω, Y s ω ∂P = ENNReal.ofReal u + PB * ENNReal.ofReal (c * s) + G s := by
    intro s
    simp only [hY]
    rw [lintegral_add_left' (f := fun ω => ENNReal.ofReal u + ind ω * ENNReal.ofReal (c * s))
        (by fun_prop),
      lintegral_add_left' (f := fun _ => ENNReal.ofReal u) aemeasurable_const, lintegral_const,
      measure_univ, mul_one, lintegral_mul_const'' _ hindm]
  -- step ii: outer integral of the elementary part
  have hmean : ∫⁻ s, ENNReal.ofReal (c * s) ∂μS = ENNReal.ofReal c * ENNReal.ofReal t := by
    simp_rw [ENNReal.ofReal_mul hc.le]
    rw [lintegral_const_mul _ ENNReal.measurable_ofReal, hμSdef, expM_mean hti]
    simp
  have houter : ∫⁻ s, ∫⁻ ω, Y s ω ∂P ∂μS =
      ENNReal.ofReal u + PB * (ENNReal.ofReal c * ENNReal.ofReal t) + ∫⁻ s, G s ∂μS := by
    simp_rw [hinner]
    rw [lintegral_add_left (f := fun s => ENNReal.ofReal u + PB * ENNReal.ofReal (c * s))
        (by fun_prop),
      lintegral_add_left (f := fun _ => ENNReal.ofReal u) measurable_const, lintegral_const,
      measure_univ, mul_one,
      lintegral_const_mul _ (by fun_prop), hmean]
  -- step iii: the block-count part
  have hterm_s : ∀ (n : ℕ) (a : ℝ), Measurable (fun s : ℝ =>
      (if 1 ≤ n then (Ici a).indicator (fun _ => (1 : ℝ≥0∞)) s else 0)) := by
    intro n a
    split_ifs
    · exact measurable_const.indicator measurableSet_Ici
    · exact measurable_const
  have hswapm : AEMeasurable (Function.uncurry fun s ω => ind ω * (ENNReal.ofReal (2 * b) * N s ω))
      (μS.prod P) := by
    refine (hindm.comp_snd).mul (aemeasurable_const.mul (AEMeasurable.ennreal_tsum (fun n => ?_)))
    by_cases hn : 1 ≤ n
    · have hm : AEMeasurable (fun p : ℝ × Ω => ({q : ℝ × ℝ | q.2 ≤ q.1}.indicator
          (fun _ => (1 : ℝ≥0∞))) (p.1, arrival W n p.2)) (μS.prod P) :=
        (measurable_const.indicator (measurableSet_le measurable_snd measurable_fst)).comp_aemeasurable
          (measurable_fst.aemeasurable.prodMk (harr n).comp_snd)
      refine hm.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hn, if_true, indicator_apply, mem_ofPred_eq, mem_Ici]
    · simp only [hn, if_false]
      exact aemeasurable_const
  have hNint : ∀ ω, (∀ k, 0 ≤ W k ω) → ∫⁻ s, N s ω ∂μS = ∑' n : ℕ,
      (if 1 ≤ n then ENNReal.ofReal (Real.exp (-(t⁻¹ * arrival W n ω))) else 0) := by
    intro ω hω
    simp only [hN]
    rw [lintegral_tsum (fun n => (hterm_s n _).aemeasurable)]
    congr 1
    funext n
    split_ifs
    · rw [lintegral_indicator_const measurableSet_Ici, one_mul, hμSdef,
        expM_Ici hti (arrival_nonneg W ω hω n)]
    · simp
  -- the independent factors
  let φ : ℕ → ℝ × Bool × Bool → ℝ≥0∞ := fun k x =>
    if k = 0 then (Iic (u / c)).indicator (fun _ => (1 : ℝ≥0∞)) x.1 *
      ENNReal.ofReal (Real.exp (-(t⁻¹ * x.1)))
    else ENNReal.ofReal (Real.exp (-(t⁻¹ * x.1)))
  have hφm : ∀ k, Measurable (φ k) := by
    intro k
    have he : Measurable (fun x : ℝ × Bool × Bool => ENNReal.ofReal (Real.exp (-(t⁻¹ * x.1)))) :=
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp ((measurable_const.mul measurable_fst).neg))
    by_cases hk : k = 0
    · simp only [φ, hk, if_true]
      exact ((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul he
    · simp only [φ, hk, if_false]
      exact he
  let h : ℕ → Ω → ℝ≥0∞ := fun k ω => φ k (W k ω, ξ k ω, ζ k ω)
  have hhind : iIndepFun h P := hprim.indep.comp φ hφm
  have hhm : ∀ k, AEMeasurable (h k) P :=
    fun k => (hφm k).comp_aemeasurable (hprim.law k).aemeasurable
  have hh0 : ∫⁻ ω, h 0 ω ∂P ≤ ENNReal.ofReal (lam * (u / c)) := by
    refine le_trans ?_ hPB
    apply lintegral_mono_ae
    filter_upwards [hgood] with ω hω
    simp only [h, φ, if_true, hind]
    calc _ ≤ (Iic (u / c)).indicator (fun _ => (1 : ℝ≥0∞)) (W 0 ω) * 1 := by
          gcongr
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_one_iff.mpr
          have := hω 0
          nlinarith
      _ = _ := mul_one _
  have hhk : ∀ k, ∫⁻ ω, h (k + 1) ω ∂P ≤ ENNReal.ofReal ρr := by
    intro k
    simp only [h, φ, Nat.succ_ne_zero, if_false]
    rw [(hlawW (k + 1)).lintegral_comp (f := fun x => ENNReal.ofReal (Real.exp (-(t⁻¹ * x))))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((measurable_const.mul measurable_id).neg))).aemeasurable]
    exact hρ
  have hprodeq : ∀ m ω, ind ω * ENNReal.ofReal (Real.exp (-(t⁻¹ * arrival W (m + 1) ω))) =
      ∏ k ∈ Finset.range (m + 1), h k ω := by
    intro m ω
    unfold arrival
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le),
      Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [h, φ, Nat.succ_ne_zero, if_false, if_true, hind]
    ring
  have hterm_ω : ∀ n : ℕ, ∫⁻ ω, ind ω *
      (if 1 ≤ n then ENNReal.ofReal (Real.exp (-(t⁻¹ * arrival W n ω))) else 0) ∂P ≤
      (if 1 ≤ n then ENNReal.ofReal ρr ^ (n - 1) * ENNReal.ofReal (lam * (u / c)) else 0) := by
    intro n
    rcases n with _ | m
    · simp
    · simp only [show 1 ≤ m + 1 by omega, if_true, Nat.add_sub_cancel]
      simp_rw [hprodeq m]
      rw [lintegral_prod_indep₀ h hhind hhm, Finset.prod_range_succ']
      gcongr
      calc ∏ k ∈ Finset.range m, ∫⁻ ω, h (k + 1) ω ∂P
          ≤ ∏ k ∈ Finset.range m, ENNReal.ofReal ρr := Finset.prod_le_prod' (fun k _ => hhk k)
        _ = _ := by simp
  have hGint : ∫⁻ s, G s ∂μS ≤
      ENNReal.ofReal (2 * b) * (ENNReal.ofReal (lam * (u / c)) * (1 - ENNReal.ofReal ρr)⁻¹) := by
    simp only [hG]
    rw [lintegral_lintegral_swap hswapm]
    have hEm : ∀ n : ℕ, AEMeasurable (fun ω => ind ω *
        (if 1 ≤ n then ENNReal.ofReal (Real.exp (-(t⁻¹ * arrival W n ω))) else 0)) P := by
      intro n
      refine hindm.mul ?_
      split_ifs
      · exact ENNReal.measurable_ofReal.comp_aemeasurable
          (Real.measurable_exp.comp_aemeasurable ((aemeasurable_const.mul (harr n)).neg))
      · exact aemeasurable_const
    calc ∫⁻ ω, ∫⁻ s, ind ω * (ENNReal.ofReal (2 * b) * N s ω) ∂μS ∂P
        = ∫⁻ ω, ENNReal.ofReal (2 * b) * ∑' n : ℕ, ind ω *
            (if 1 ≤ n then ENNReal.ofReal (Real.exp (-(t⁻¹ * arrival W n ω))) else 0) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hgood] with ω hω
          have hi : ind ω ≠ ⊤ := by
            simp only [hind, indicator_apply]
            split_ifs <;> simp
          rw [lintegral_const_mul' _ _ hi, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            hNint ω hω, ENNReal.tsum_mul_left]
          ring
      _ = ENNReal.ofReal (2 * b) * ∑' n : ℕ, ∫⁻ ω, ind ω *
            (if 1 ≤ n then ENNReal.ofReal (Real.exp (-(t⁻¹ * arrival W n ω))) else 0) ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hEm]
      _ ≤ ENNReal.ofReal (2 * b) * ∑' n : ℕ,
            (if 1 ≤ n then ENNReal.ofReal ρr ^ (n - 1) * ENNReal.ofReal (lam * (u / c)) else 0) := by
          gcongr with n
          exact hterm_ω n
      _ = ENNReal.ofReal (2 * b) * (ENNReal.ofReal (lam * (u / c)) * (1 - ENNReal.ofReal ρr)⁻¹) := by
          congr 1
          rw [tsum_eq_zero_add' ENNReal.summable]
          simp only [show ¬ (1 ≤ 0) by omega, if_false, zero_add,
            show ∀ m : ℕ, 1 ≤ m + 1 from fun m => by omega, if_true, Nat.add_sub_cancel]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]
  have hK : 0 ≤ 1 + lam * t + 2 * b * (lam / c) * (1 - ρr)⁻¹ := by
    have : 0 < 1 - ρr := by linarith
    positivity
  have htot : ∫⁻ s, ∫⁻ ω, Y s ω ∂P ∂μS ≤
      ENNReal.ofReal ((1 + lam * t + 2 * b * (lam / c) * (1 - ρr)⁻¹) * u) := by
    rw [houter]
    have h1ρ : (1 - ENNReal.ofReal ρr) = ENNReal.ofReal (1 - ρr) := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ hρr0]
    have hpos : 0 < 1 - ρr := by linarith
    calc ENNReal.ofReal u + PB * (ENNReal.ofReal c * ENNReal.ofReal t) + ∫⁻ s, G s ∂μS
        ≤ ENNReal.ofReal u + ENNReal.ofReal (lam * (u / c)) * (ENNReal.ofReal c * ENNReal.ofReal t) +
          ENNReal.ofReal (2 * b) * (ENNReal.ofReal (lam * (u / c)) * (1 - ENNReal.ofReal ρr)⁻¹) := by
          gcongr
      _ = _ := by
          rw [h1ρ, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul hc.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hu (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
  -- the outer bound
  have hstep1 : |Vhat P W ξ ζ c b u t z| ≤
      (∫⁻ s, ∫⁻ ω, Y s ω ∂P ∂μS).toReal := by
    have hA := norm_integral_le_lintegral_norm (μ := μS) (fun s => V P W ξ ζ c b u s z)
    rw [Real.norm_eq_abs] at hA
    refine hA.trans (ENNReal.toReal_mono ?_ ?_)
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot
    · apply lintegral_mono_ae
      filter_upwards [expM_ae_nonneg hti] with s hs
      have hB := norm_integral_le_lintegral_norm (μ := P)
        (fun ω => if ENNReal.ofReal s < ruinTime W ξ ζ c b u z ω
          then surplus W ξ ζ c b u s z ω else 0)
      calc ENNReal.ofReal ‖V P W ξ ζ c b u s z‖
          ≤ ENNReal.ofReal (ENNReal.toReal (∫⁻ ω, ENNReal.ofReal
            ‖(if ENNReal.ofReal s < ruinTime W ξ ζ c b u z ω
              then surplus W ξ ζ c b u s z ω else 0)‖ ∂P)) := ENNReal.ofReal_le_ofReal hB
        _ ≤ ∫⁻ ω, ENNReal.ofReal
            ‖(if ENNReal.ofReal s < ruinTime W ξ ζ c b u z ω
              then surplus W ξ ζ c b u s z ω else 0)‖ ∂P := ENNReal.ofReal_toReal_le
        _ ≤ ∫⁻ ω, Y s ω ∂P := by
            apply lintegral_mono_ae
            filter_upwards [hgood] with ω hω
            exact hpt s hs ω hω
  refine hstep1.trans ?_
  calc (∫⁻ s, ∫⁻ ω, Y s ω ∂P ∂μS).toReal
      ≤ (ENNReal.ofReal ((1 + lam * t + 2 * b * (lam / c) * (1 - ρr)⁻¹) * u)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top htot
    _ = _ := ENNReal.toReal_ofReal (by positivity)
