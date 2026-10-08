-- Prove2me | solution 1 for PoissonDirichlet.Ratio.poisson_ratio_beta
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:32:37.785651+00:00
-- url     : https://prove2.me/submissions/92d2381b-1938-4428-8624-21eff16499ba

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting

open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.Ratio

open Set

/-- Core integral: ∫_{[a,∞)} exp(-(1+s) y) dy = exp(-(1+s) a)/(1+s). -/
lemma prb_core (s a : ℝ) (hs : 0 ≤ s) :
    ∫⁻ y in Ici a, ENNReal.ofReal (Real.exp (-(1 + s) * y)) =
      ENNReal.ofReal (Real.exp (-(1 + s) * a) / (1 + s)) := by
  have h1 : (0:ℝ) < 1 + s := by linarith
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-(1 + s) * y)) (Ici a) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact exp_neg_integrableOn_Ioi a h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))]
  congr 1
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith)]
  field_simp

lemma prb_meas_gpdf : Measurable (gammaPDF 1 1) := by
  unfold gammaPDF; exact (measurable_gammaPDFReal 1 1).ennreal_ofReal

/-- Laplace transform of the Exp(1) tail. -/
lemma prb_expTail (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) * {y : ℝ | a ≤ y}.indicator 1 y ∂(expMeasure 1) =
      ENNReal.ofReal (Real.exp (-(1 + s) * a) / (1 + s)) := by
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y)) * {y : ℝ | a ≤ y}.indicator 1 y) :=
    Measurable.mul (by fun_prop) (measurable_one.indicator (measurableSet_Ici (a := a)))
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ prb_meas_gpdf hm]
  rw [← prb_core s a hs, ← lintegral_indicator measurableSet_Ici]
  congr 1
  ext y
  simp only [Pi.mul_apply]
  by_cases hy : a ≤ y
  · have hy0 : 0 ≤ y := le_trans ha hy
    rw [indicator_of_mem (show y ∈ Ici a from hy), indicator_of_mem (show y ∈ {y : ℝ | a ≤ y} from hy)]
    rw [show gammaPDF 1 1 y = exponentialPDF 1 y from rfl, exponentialPDF_of_nonneg hy0]
    simp only [Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_mul (by positivity), one_mul, ← Real.exp_add]
    congr 2; ring
  · rw [indicator_of_notMem (show y ∉ Ici a from hy),
      indicator_of_notMem (show y ∉ {y : ℝ | a ≤ y} from hy)]
    simp

/-- Laplace transform of Exp(1). -/
lemma prb_expLaplace (s : ℝ) (hs : 0 ≤ s) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(expMeasure 1) =
      ENNReal.ofReal (1 / (1 + s)) := by
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ prb_meas_gpdf
    (by fun_prop)]
  have := prb_core s 0 hs
  simp only [mul_zero, Real.exp_zero] at this
  rw [← this, ← lintegral_indicator measurableSet_Ici]
  congr 1
  ext y
  simp only [Pi.mul_apply]
  by_cases hy : 0 ≤ y
  · rw [indicator_of_mem (show y ∈ Ici 0 from hy)]
    rw [show gammaPDF 1 1 y = exponentialPDF 1 y from rfl, exponentialPDF_of_nonneg hy]
    rw [← ENNReal.ofReal_mul (by positivity), one_mul, ← Real.exp_add]
    congr 2; ring
  · rw [indicator_of_notMem (show y ∉ Ici 0 from hy)]
    rw [show gammaPDF 1 1 y = exponentialPDF 1 y from rfl, exponentialPDF_of_neg (by linarith)]
    simp

/-- Exp(1) is a.s. positive. -/
lemma prb_exp_Iic_zero : expMeasure 1 (Iic 0) = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iic]
  have h : Iic (0:ℝ) = Iio 0 ∪ {0} := by ext x; simp [le_iff_lt_or_eq]
  rw [h, Measure.restrict_union (by simp) (measurableSet_singleton 0)]
  rw [lintegral_add_measure, lintegral_gammaPDF_of_nonpos le_rfl]
  simp

/-- beta(k+1,1) normalisation. -/
lemma prb_beta_eq (k : ℕ) : beta ((k:ℝ) + 1) 1 = 1 / ((k:ℝ) + 1) := by
  rw [beta, Real.Gamma_one]
  have h1 : Real.Gamma ((k:ℝ) + 1) = (k.factorial : ℝ) := Real.Gamma_nat_eq_factorial k
  have h2 : Real.Gamma ((k:ℝ) + 1 + 1) = ((k+1).factorial : ℝ) := by
    have := Real.Gamma_nat_eq_factorial (k+1)
    push_cast at this; exact this
  rw [h1, h2, Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The beta(k+1,1) CDF. -/
lemma prb_beta_cdf (k : ℕ) (a : ℝ) :
    betaMeasure ((k:ℝ) + 1) 1 (Iic a) =
      if a ≤ 0 then 0 else ENNReal.ofReal ((min a 1) ^ (k + 1)) := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Iic]
  split_ifs with ha
  · rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)]
    · simp
    · intro x hx
      exact betaPDF_eq_zero_of_nonpos (le_trans hx ha)
  · push_neg at ha
    set b := min a 1 with hb
    have hb0 : 0 < b := lt_min ha one_pos
    have hb1 : b ≤ 1 := min_le_right _ _
    have hba : b ≤ a := min_le_left _ _
    -- the integrand on Ioc 0 b
    have hint : ∫⁻ x in Ioc 0 b, ENNReal.ofReal (((k:ℝ) + 1) * x ^ k) = ENNReal.ofReal (b ^ (k+1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [← intervalIntegral.integral_of_le hb0.le, intervalIntegral.integral_const_mul,
          integral_pow]
        field_simp
        ring
      · have : ContinuousOn (fun x : ℝ => ((k:ℝ) + 1) * x ^ k) (Icc 0 b) := by fun_prop
        exact (integrableOn_Icc_iff_integrableOn_Ioc).1 this.integrableOn_Icc
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun x hx => by
          have := hx.1; positivity)
    rw [← hint, ← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr_ae
    have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      rw [ae_iff]; simp
    filter_upwards [h1] with x hx1
    by_cases hx0 : x ≤ 0
    · rw [indicator_of_notMem (show x ∉ Ioc 0 b from fun h => by linarith [h.1])]
      by_cases hxa : x ∈ Iic a
      · rw [indicator_of_mem hxa]; exact betaPDF_eq_zero_of_nonpos hx0
      · rw [indicator_of_notMem hxa]
    push_neg at hx0
    by_cases hx1' : 1 ≤ x
    · rw [indicator_of_notMem (show x ∉ Ioc 0 b from fun h => hx1 (le_antisymm (le_trans h.2 hb1) hx1'))]
      by_cases hxa : x ∈ Iic a
      · rw [indicator_of_mem hxa]; exact betaPDF_eq_zero_of_one_le hx1'
      · rw [indicator_of_notMem hxa]
    push_neg at hx1'
    by_cases hxa : x ≤ a
    · have hxb : x ∈ Ioc 0 b := ⟨hx0, le_min hxa hx1'.le⟩
      rw [indicator_of_mem hxb, indicator_of_mem (show x ∈ Iic a from hxa)]
      rw [betaPDF_of_pos_lt_one hx0 hx1', prb_beta_eq]
      congr 1
      simp only [add_sub_cancel_right, sub_self, Real.rpow_zero, mul_one, one_div, inv_inv]
      rw [Real.rpow_natCast]
    · rw [indicator_of_notMem (show x ∉ Iic a from hxa),
        indicator_of_notMem (show x ∉ Ioc 0 b from fun h => hxa (le_trans h.2 hba))]


/-- Partial sums of the arrivals. -/
def prbX {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), ε i ω

/-- The ratio event up to index `m`. -/
def prbE {Ω : Type*} (ε : ℕ → Ω → ℝ) (r : ℕ → ℝ) (m : ℕ) : Set Ω :=
  ⋂ k ∈ Finset.range m, {ω | prbX ε ω k ≤ r k * prbX ε ω (k + 1)}

lemma prbX_measurable {Ω : Type*} [MeasurableSpace Ω] (ε : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i)) (k : ℕ) : Measurable (fun ω => prbX ε ω k) := by
  unfold prbX
  exact Finset.measurable_sum _ (fun i _ => hmeas i)

lemma prbE_measurable {Ω : Type*} [MeasurableSpace Ω] (ε : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i)) (r : ℕ → ℝ) (m : ℕ) : MeasurableSet (prbE ε r m) := by
  unfold prbE
  refine Finset.measurableSet_biInter _ (fun k _ => ?_)
  exact measurableSet_le (prbX_measurable ε hmeas k)
    ((prbX_measurable ε hmeas (k+1)).const_mul _)

lemma prbX_succ {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) :
    prbX ε ω (k + 1) = prbX ε ω k + ε (k + 1) ω := by
  unfold prbX; rw [Finset.sum_range_succ]

lemma prbE_zero {Ω : Type*} (ε : ℕ → Ω → ℝ) (r : ℕ → ℝ) : prbE ε r 0 = Set.univ := by
  unfold prbE; simp

lemma mem_prbE_succ {Ω : Type*} (ε : ℕ → Ω → ℝ) (r : ℕ → ℝ) (m : ℕ) (ω : Ω) :
    ω ∈ prbE ε r (m + 1) ↔ ω ∈ prbE ε r m ∧ prbX ε ω m ≤ r m * prbX ε ω (m + 1) := by
  unfold prbE
  rw [Finset.range_add_one, Finset.set_biInter_insert]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/-- One-step integration over an independent Exp(1) variable. -/
lemma prb_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → (ℕ → ℝ)) (hY : Measurable Y) (Z : Ω → ℝ) (hZ : Measurable Z)
    (hind : IndepFun Y Z P) (hlaw : HasLaw Z (expMeasure 1) P)
    (F : (ℕ → ℝ) → ENNReal) (hF : Measurable F) (g : (ℕ → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ v, 0 ≤ g v) (s : ℝ) (hs : 0 ≤ s) :
    ∫⁻ ω, F (Y ω) * (ENNReal.ofReal (Real.exp (-s * Z ω)) *
        {ω | g (Y ω) ≤ Z ω}.indicator 1 ω) ∂P
      = ∫⁻ ω, F (Y ω) * ENNReal.ofReal (Real.exp (-(1 + s) * g (Y ω)) / (1 + s)) ∂P := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  let H : (ℕ → ℝ) × ℝ → ENNReal := fun p =>
    F p.1 * (ENNReal.ofReal (Real.exp (-s * p.2)) * {p : (ℕ → ℝ) × ℝ | g p.1 ≤ p.2}.indicator 1 p)
  have hset : MeasurableSet {p : (ℕ → ℝ) × ℝ | g p.1 ≤ p.2} :=
    measurableSet_le (hg.comp measurable_fst) measurable_snd
  have hH : Measurable H := by
    refine (hF.comp measurable_fst).mul (Measurable.mul ?_ (measurable_one.indicator hset))
    exact (Real.measurable_exp.comp (measurable_snd.const_mul _)).ennreal_ofReal
  have h1 : (fun ω => F (Y ω) * (ENNReal.ofReal (Real.exp (-s * Z ω)) *
        {ω | g (Y ω) ≤ Z ω}.indicator 1 ω)) = fun ω => H (Y ω, Z ω) := by
    funext ω
    simp only [H, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [h1, ← lintegral_map hH (hY.prodMk hZ),
    hind.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable, hlaw.map_eq,
    lintegral_prod _ hH.aemeasurable]
  have h2 : ∀ y : ℕ → ℝ, ∫⁻ z, H (y, z) ∂(expMeasure 1) =
      F y * ENNReal.ofReal (Real.exp (-(1 + s) * g y) / (1 + s)) := by
    intro y
    have : (fun z => H (y, z)) = fun z => F y * (ENNReal.ofReal (Real.exp (-s * z)) *
        {z : ℝ | g y ≤ z}.indicator 1 z) := by
      funext z
      simp only [H, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    have hm : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-s * z)) *
        {z : ℝ | g y ≤ z}.indicator 1 z) :=
      Measurable.mul (by fun_prop) (measurable_one.indicator (measurableSet_Ici (a := g y)))
    rw [this, lintegral_const_mul _ hm, prb_expTail s (g y) hs (hg0 y)]
  simp_rw [h2]
  have hm2 : Measurable (fun x : ℕ → ℝ => F x *
      ENNReal.ofReal (Real.exp (-(1 + s) * g x) / (1 + s))) :=
    hF.mul ((Real.measurable_exp.comp (hg.const_mul _)).div_const _).ennreal_ofReal
  exact lintegral_map hm2 hY

/-- The joint Laplace-type functional of the ratio events. -/
lemma prb_claim {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) (hpos : ∀ i ω, 0 ≤ ε i ω)
    (hind : iIndepFun ε P) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P)
    (r : ℕ → ℝ) (hr0 : ∀ k, 0 < r k) (hr1 : ∀ k, r k ≤ 1) (m : ℕ) :
    ∀ s : ℝ, 0 ≤ s →
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * prbX ε ω m)) * (prbE ε r m).indicator 1 ω ∂P =
      ENNReal.ofReal ((∏ k ∈ Finset.range m, r k ^ (k + 1)) / (1 + s) ^ (m + 1)) := by
  induction m with
  | zero =>
    intro s hs
    rw [prbE_zero]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, Finset.range_zero,
      Finset.prod_empty, zero_add, pow_one]
    have : (fun ω => ENNReal.ofReal (Real.exp (-s * prbX ε ω 0))) =
        fun ω => ENNReal.ofReal (Real.exp (-s * ε 0 ω)) := by
      funext ω; unfold prbX; simp
    rw [this, ← lintegral_map (f := fun y => ENNReal.ofReal (Real.exp (-s * y))) (by fun_prop)
      (hmeas 0), (hlaw 0).map_eq, prb_expLaplace s hs]
  | succ m ih =>
    intro s hs
    have hrm := hr0 m
    set c : ℝ := (1 - r m) / r m with hc
    have hc0 : 0 ≤ c := div_nonneg (by linarith [hr1 m]) hrm.le
    -- the tuple of the first m+1 variables
    let S : Finset ℕ := Finset.range (m + 1)
    let Y : Ω → (ℕ → ℝ) := fun ω i => if h : i ∈ S then ε i ω else 0
    have hY : Measurable Y := by
      refine measurable_pi_lambda _ (fun i => ?_)
      by_cases h : i ∈ S
      · have : (fun ω => Y ω i) = ε i := by funext ω; simp [Y, h]
        rw [this]; exact hmeas i
      · have : (fun ω => Y ω i) = fun _ => 0 := by funext ω; simp [Y, h]
        rw [this]; exact measurable_const
    let Z : Ω → ℝ := ε (m + 1)
    have hYZ : IndepFun Y Z P := by
      have hdisj : Disjoint S {m + 1} := by
        simp [S, Finset.disjoint_singleton_right]
      have h := hind.indepFun_finset S {m + 1} hdisj hmeas
      let φ : (S → ℝ) → (ℕ → ℝ) := fun v i => if h : i ∈ S then v ⟨i, h⟩ else 0
      have hφ : Measurable φ := by
        refine measurable_pi_lambda _ (fun i => ?_)
        by_cases h : i ∈ S
        · simp only [φ, h, dite_true]; exact measurable_pi_apply _
        · simp only [φ, h, dite_false]; exact measurable_const
      let ψ : (({m + 1} : Finset ℕ) → ℝ) → ℝ := fun w => w ⟨m + 1, Finset.mem_singleton_self _⟩
      have hψ : Measurable ψ := measurable_pi_apply _
      exact h.comp hφ hψ
    -- sums as functions of the tuple
    let Sv : (ℕ → ℝ) → ℕ → ℝ := fun v k => ∑ i ∈ Finset.range (k + 1), v i
    have hSv : ∀ k, Measurable (fun v => Sv v k) := fun k =>
      Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
    have hYS : ∀ ω k, k ≤ m → Sv (Y ω) k = prbX ε ω k := by
      intro ω k hk
      unfold prbX
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i ∈ S := by
        simp only [S, Finset.mem_range] at hi ⊢; omega
      simp [Y, this]
    let Ev : Set (ℕ → ℝ) := ⋂ k ∈ Finset.range m, {v | Sv v k ≤ r k * Sv v (k + 1)}
    have hEv : MeasurableSet Ev :=
      Finset.measurableSet_biInter _ (fun k _ => measurableSet_le (hSv k) ((hSv (k+1)).const_mul _))
    have hmemEv : ∀ ω, Y ω ∈ Ev ↔ ω ∈ prbE ε r m := by
      intro ω
      simp only [Ev, prbE, Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range]
      constructor
      · intro h k hk; rw [← hYS ω k (by omega), ← hYS ω (k+1) (by omega)]; exact h k hk
      · intro h k hk; rw [hYS ω k (by omega), hYS ω (k+1) (by omega)]; exact h k hk
    let F : (ℕ → ℝ) → ENNReal := fun v =>
      ENNReal.ofReal (Real.exp (-s * Sv v m)) * Ev.indicator 1 v
    have hF : Measurable F := by
      refine Measurable.mul ?_ (measurable_one.indicator hEv)
      exact (Real.measurable_exp.comp ((hSv m).const_mul _)).ennreal_ofReal
    let g : (ℕ → ℝ) → ℝ := fun v => c * max (Sv v m) 0
    have hg : Measurable g := ((hSv m).max measurable_const).const_mul _
    have hg0 : ∀ v, 0 ≤ g v := fun v => mul_nonneg hc0 (le_max_right _ _)
    have hXnn : ∀ ω k, 0 ≤ prbX ε ω k := fun ω k =>
      Finset.sum_nonneg (fun i _ => hpos i ω)
    have hgY : ∀ ω, g (Y ω) = c * prbX ε ω m := by
      intro ω
      simp only [g]
      rw [hYS ω m le_rfl, max_eq_left (hXnn ω m)]
    have hFY : ∀ ω, F (Y ω) =
        ENNReal.ofReal (Real.exp (-s * prbX ε ω m)) * (prbE ε r m).indicator 1 ω := by
      intro ω
      simp only [F]
      rw [hYS ω m le_rfl]
      congr 1
      by_cases h : ω ∈ prbE ε r m
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmemEv ω).2 h)]; rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmemEv ω).1 h'))]
    -- the key pointwise identity
    have hpt : ∀ ω, ENNReal.ofReal (Real.exp (-s * prbX ε ω (m + 1))) *
        (prbE ε r (m + 1)).indicator 1 ω =
        F (Y ω) * (ENNReal.ofReal (Real.exp (-s * Z ω)) * {ω | g (Y ω) ≤ Z ω}.indicator 1 ω) := by
      intro ω
      rw [hFY ω]
      have hexp : ENNReal.ofReal (Real.exp (-s * prbX ε ω (m + 1))) =
          ENNReal.ofReal (Real.exp (-s * prbX ε ω m)) * ENNReal.ofReal (Real.exp (-s * Z ω)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, prbX_succ]
        congr 2; simp only [Z]; ring
      rw [hexp]
      have hiff : ω ∈ {ω | g (Y ω) ≤ Z ω} ↔ prbX ε ω m ≤ r m * prbX ε ω (m + 1) := by
        simp only [Set.mem_setOf_eq, Z, hgY, hc, prbX_succ]
        rw [div_mul_eq_mul_div, div_le_iff₀ hrm]
        constructor <;> intro h <;> nlinarith
      by_cases h1 : ω ∈ prbE ε r m
      · by_cases h2 : prbX ε ω m ≤ r m * prbX ε ω (m + 1)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hiff.2 h2),
            Set.indicator_of_mem ((mem_prbE_succ ε r m ω).2 ⟨h1, h2⟩)]
          simp only [Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem (fun h => h2 (hiff.1 h)),
            Set.indicator_of_notMem (fun h => h2 ((mem_prbE_succ ε r m ω).1 h).2)]
          simp
      · rw [Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (fun h => h1 ((mem_prbE_succ ε r m ω).1 h).1)]
        simp
    simp_rw [hpt]
    rw [prb_step P Y hY Z (hmeas (m+1)) hYZ (hlaw (m+1)) F hF g hg hg0 s hs]
    -- reduce to the induction hypothesis
    set s' : ℝ := s + (1 + s) * c with hs'
    have hs'0 : 0 ≤ s' := by positivity
    have h1s' : 1 + s' = (1 + s) / r m := by
      rw [hs', hc]; field_simp; ring
    have hpt2 : ∀ ω, F (Y ω) * ENNReal.ofReal (Real.exp (-(1 + s) * g (Y ω)) / (1 + s)) =
        ENNReal.ofReal (1 / (1 + s)) *
          (ENNReal.ofReal (Real.exp (-s' * prbX ε ω m)) * (prbE ε r m).indicator 1 ω) := by
      intro ω
      rw [hFY ω, hgY ω]
      have : ENNReal.ofReal (Real.exp (-(1 + s) * (c * prbX ε ω m)) / (1 + s)) =
          ENNReal.ofReal (1 / (1 + s)) * ENNReal.ofReal (Real.exp (-(1 + s) * (c * prbX ε ω m))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      rw [this]
      have : ENNReal.ofReal (Real.exp (-s' * prbX ε ω m)) =
          ENNReal.ofReal (Real.exp (-s * prbX ε ω m)) *
            ENNReal.ofReal (Real.exp (-(1 + s) * (c * prbX ε ω m))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hs']
        congr 2; ring
      rw [this]; ring
    simp_rw [hpt2]
    have hm3 : Measurable (fun ω => ENNReal.ofReal (Real.exp (-s' * prbX ε ω m)) *
        (prbE ε r m).indicator 1 ω) :=
      Measurable.mul
        (Real.measurable_exp.comp ((prbX_measurable ε hmeas m).const_mul _)).ennreal_ofReal
        (measurable_one.indicator (prbE_measurable ε hmeas r m))
    rw [lintegral_const_mul _ hm3, ih s' hs'0]
    rw [← ENNReal.ofReal_mul (by positivity), Finset.prod_range_succ, h1s']
    congr 1
    have h1 : (0:ℝ) < 1 + s := by linarith
    have h2 : r m ≠ 0 := hrm.ne'
    rw [div_pow]
    field_simp
    ring

/-- Probability of the ratio event. -/
lemma prb_measE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) (hpos : ∀ i ω, 0 ≤ ε i ω)
    (hind : iIndepFun ε P) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P)
    (r : ℕ → ℝ) (hr0 : ∀ k, 0 < r k) (hr1 : ∀ k, r k ≤ 1) (m : ℕ) :
    P (prbE ε r m) = ENNReal.ofReal (∏ k ∈ Finset.range m, r k ^ (k + 1)) := by
  have := prb_claim P ε hmeas hpos hind hlaw r hr0 hr1 m 0 le_rfl
  simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul, add_zero, one_pow,
    div_one] at this
  rw [← this, lintegral_indicator_one (prbE_measurable ε hmeas r m)]


/-- The ratio of consecutive partial sums. -/
noncomputable def prbR {Ω : Type*} (ε : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := prbX ε ω k / prbX ε ω (k + 1)

lemma prbR_measurable {Ω : Type*} [MeasurableSpace Ω] (ε : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i)) (k : ℕ) : Measurable (prbR ε k) :=
  (prbX_measurable ε hmeas k).div (prbX_measurable ε hmeas (k+1))

lemma prb_ae_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) :
    ∀ᵐ ω ∂P, ∀ i, 0 < ε i ω := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have : {ω | ¬ 0 < ε i ω} = {ω | ε i ω ≤ 0} := by ext; simp
  rw [this, (hlaw i).measure_eq (p := fun x => x ≤ 0) measurableSet_Iic]
  exact prb_exp_Iic_zero

lemma prbX_pos {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (h : ∀ i, 0 < ε i ω) (k : ℕ) :
    0 < prbX ε ω k := by
  unfold prbX
  exact Finset.sum_pos (fun i _ => h i) ⟨0, Finset.mem_range.2 (Nat.succ_pos k)⟩

lemma prbX_mono {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (h : ∀ i, 0 ≤ ε i ω) (k : ℕ) :
    prbX ε ω k ≤ prbX ε ω (k + 1) := by
  rw [prbX_succ]; linarith [h (k+1)]

/-- Measure of a finite intersection of ratio events. -/
lemma prb_meas_inter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) (hpos : ∀ i ω, 0 ≤ ε i ω)
    (hind : iIndepFun ε P) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P)
    (S : Finset ℕ) (r : ℕ → ℝ) (hrS : ∀ k ∈ S, 0 < r k) :
    P (⋂ k ∈ S, {ω | prbR ε k ω ≤ r k}) =
      ENNReal.ofReal (∏ k ∈ S, (min (r k) 1) ^ (k + 1)) := by
  classical
  let r' : ℕ → ℝ := fun k => if k ∈ S then min (r k) 1 else 1
  have hr'0 : ∀ k, 0 < r' k := by
    intro k; simp only [r']; split_ifs with h
    · exact lt_min (hrS k h) one_pos
    · exact one_pos
  have hr'1 : ∀ k, r' k ≤ 1 := by
    intro k; simp only [r']; split_ifs with h
    · exact min_le_right _ _
    · exact le_rfl
  let m : ℕ := S.sup id + 1
  have hSm : ∀ k ∈ S, k < m := fun k hk =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hae := prb_ae_pos P ε hlaw
  have hset : (⋂ k ∈ S, {ω | prbR ε k ω ≤ r k}) =ᵐ[P] prbE ε r' m := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with ω hω
    have hXpos := prbX_pos ε ω hω
    have hXmono := prbX_mono ε ω (fun i => (hω i).le)
    simp only [prbE, Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range, prbR]
    constructor
    · intro h k hk
      simp only [r']
      split_ifs with hkS
      · have h1 := (div_le_iff₀ (hXpos (k+1))).1 (h k hkS)
        rcases min_choice (r k) 1 with hm | hm <;> rw [hm]
        · exact h1
        · rw [one_mul]; exact hXmono k
      · rw [one_mul]; exact hXmono k
    · intro h k hk
      have h1 := h k (hSm k hk)
      simp only [r', if_pos hk] at h1
      rw [div_le_iff₀ (hXpos (k+1))]
      exact le_trans h1 (mul_le_mul_of_nonneg_right (min_le_left _ _) (hXpos (k+1)).le)
  rw [measure_congr hset, prb_measE P ε hmeas hpos hind hlaw r' hr'0 hr'1 m]
  congr 1
  rw [← Finset.prod_subset (s₁ := S) (s₂ := Finset.range m)]
  · exact Finset.prod_congr rfl (fun k hk => by simp [r', hk])
  · intro k hk; exact Finset.mem_range.2 (hSm k hk)
  · intro k _ hk; simp [r', hk]

lemma prb_meas_single {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) (hpos : ∀ i ω, 0 ≤ ε i ω)
    (hind : iIndepFun ε P) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P)
    (k : ℕ) (a : ℝ) :
    P {ω | prbR ε k ω ≤ a} = if a ≤ 0 then 0 else ENNReal.ofReal ((min a 1) ^ (k + 1)) := by
  split_ifs with ha
  · have hae := prb_ae_pos P ε hlaw
    have : ∀ᵐ ω ∂P, ω ∉ {ω | prbR ε k ω ≤ a} := by
      filter_upwards [hae] with ω hω
      have hXpos := prbX_pos ε ω hω
      simp only [Set.mem_setOf_eq, not_le, prbR]
      exact lt_of_le_of_lt ha (div_pos (hXpos k) (hXpos (k+1)))
    exact ae_iff.1 this |> fun h => by simpa using h
  · push_neg at ha
    have := prb_meas_inter P ε hmeas hpos hind hlaw {k} (fun _ => a) (fun _ _ => ha)
    simpa using this

/-- Independence of the ratios (measurable, nonnegative version). -/
lemma prb_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) (hpos : ∀ i ω, 0 ≤ ε i ω)
    (hind : iIndepFun ε P) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) :
    iIndepFun (prbR ε) P := by
  classical
  rw [iIndepFun_iff_iIndep]
  let π : ℕ → Set (Set Ω) := fun k => {s | ∃ t ∈ Set.range (Iic : ℝ → Set ℝ), prbR ε k ⁻¹' t = s}
  refine iIndepSets.iIndep (fun k => (prbR_measurable ε hmeas k).comap_le) π
    (fun k => isPiSystem_Iic.comap _) ?_ ?_
  · intro k
    show MeasurableSpace.comap (prbR ε k) (borel ℝ) = _
    rw [borel_eq_generateFrom_Iic, MeasurableSpace.comap_generateFrom]
    rfl
  · rw [iIndepSets_iff]
    intro S f hf
    have : ∀ i, ∃ a : ℝ, i ∈ S → f i = {ω | prbR ε i ω ≤ a} := by
      intro i
      by_cases hi : i ∈ S
      · obtain ⟨t, ⟨a, rfl⟩, hft⟩ := hf i hi
        exact ⟨a, fun _ => hft.symm⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose a ha using this
    have h1 : (⋂ i ∈ S, f i) = ⋂ i ∈ S, {ω | prbR ε i ω ≤ a i} := by
      apply Set.iInter₂_congr
      intro i hi; exact ha i hi
    have h2 : ∏ i ∈ S, P (f i) = ∏ i ∈ S, P {ω | prbR ε i ω ≤ a i} :=
      Finset.prod_congr rfl (fun i hi => by rw [ha i hi])
    rw [h1, h2]
    by_cases hex : ∃ k ∈ S, a k ≤ 0
    · obtain ⟨k, hkS, hk⟩ := hex
      have h0 : P {ω | prbR ε k ω ≤ a k} = 0 := by
        rw [prb_meas_single P ε hmeas hpos hind hlaw, if_pos hk]
      rw [Finset.prod_eq_zero hkS h0]
      exact measure_mono_null (Set.biInter_subset_of_mem hkS) h0
    · push_neg at hex
      rw [prb_meas_inter P ε hmeas hpos hind hlaw S a hex,
        ENNReal.ofReal_prod_of_nonneg (fun k hk => pow_nonneg (le_min (hex k hk).le one_pos.le) _)]
      refine Finset.prod_congr rfl (fun k hk => ?_)
      rw [prb_meas_single P ε hmeas hpos hind hlaw, if_neg (not_le.2 (hex k hk))]

/-- Law of the ratios (measurable, nonnegative version). -/
lemma prb_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) (hpos : ∀ i ω, 0 ≤ ε i ω)
    (hind : iIndepFun ε P) (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) (k : ℕ) :
    HasLaw (prbR ε k) (betaMeasure ((k : ℝ) + 1) 1) P where
  aemeasurable := (prbR_measurable ε hmeas k).aemeasurable
  map_eq := by
    refine Measure.ext_of_Iic _ _ (fun a => ?_)
    rw [Measure.map_apply (prbR_measurable ε hmeas k) measurableSet_Iic, prb_beta_cdf]
    exact prb_meas_single P ε hmeas hpos hind hlaw k a

/-- The main statement, with only a.e.-measurable arrivals. -/
theorem poisson_ratio_beta_core {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ)
    (hind : iIndepFun ε P)
    (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) :
    let X : Ω → ℕ → ℝ := fun ω k =>
      ∑ i ∈ Finset.range (k + 1), ε i ω
    iIndepFun (fun k ω => X ω k / X ω (k + 1)) P ∧
      ∀ k : ℕ, HasLaw (fun ω => X ω k / X ω (k + 1))
        (betaMeasure ((k : ℝ) + 1) 1) P := by
  intro X
  let ε' : ℕ → Ω → ℝ := fun i ω => max ((hlaw i).aemeasurable.mk (ε i) ω) 0
  have hmeas' : ∀ i, Measurable (ε' i) := fun i =>
    (hlaw i).aemeasurable.measurable_mk.max measurable_const
  have hpos' : ∀ i ω, 0 ≤ ε' i ω := fun i ω => le_max_right _ _
  have hae := prb_ae_pos P ε hlaw
  have hεε' : ∀ i, ε' i =ᵐ[P] ε i := by
    intro i
    filter_upwards [(hlaw i).aemeasurable.ae_eq_mk, hae] with ω h1 h2
    simp only [ε']
    rw [← h1, max_eq_left (h2 i).le]
  have hind' : iIndepFun ε' P := hind.congr (fun i => (hεε' i).symm)
  have hlaw' : ∀ i, HasLaw (ε' i) (expMeasure 1) P := fun i => (hlaw i).congr (hεε' i)
  have hRR : ∀ k, prbR ε' k =ᵐ[P] prbR ε k := by
    intro k
    have hall : ∀ᵐ ω ∂P, ∀ i, ε' i ω = ε i ω := ae_all_iff.2 hεε'
    filter_upwards [hall] with ω hω
    simp only [prbR, prbX, hω]
  refine ⟨?_, ?_⟩
  · have := (prb_indep P ε' hmeas' hpos' hind' hlaw').congr hRR
    exact this
  · intro k
    exact (prb_law P ε' hmeas' hpos' hind' hlaw' k).congr (hRR k).symm

end PoissonDirichlet.Ratio

open PoissonDirichlet.Ratio


theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ)
    (hind : iIndepFun ε P)
    (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) :
    let X : Ω → ℕ → ℝ := fun ω k =>
      ∑ i ∈ Finset.range (k + 1), ε i ω
    iIndepFun (fun k ω => X ω k / X ω (k + 1)) P ∧
      ∀ k : ℕ, HasLaw (fun ω => X ω k / X ω (k + 1))
        (betaMeasure ((k : ℝ) + 1) 1) P := by
  exact poisson_ratio_beta_core P ε hind hlaw
