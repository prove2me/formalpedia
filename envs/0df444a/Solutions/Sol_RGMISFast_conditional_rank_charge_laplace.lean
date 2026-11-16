-- Prove2me | solution 1 for RGMISFast.conditional_rank_charge_laplace
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T04:38:49.173872+00:00
-- url     : https://prove2.me/submissions/8c8e965c-4c85-4ea3-a2f9-9bd6e23544af

import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_condLaw
import Definitions.Def_RGMISFast_gammaA
import Mathlib
set_option maxHeartbeats 1000000

-- Source: Solutions.ExponentialArrivals
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ExponentialArrivals
open Classical
instance expOne_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)
instance expOne_nullSingleton : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  infer_instance

lemma expOne_real_Iio (s : ℝ) (hs : 0 ≤ s) :
    (expMeasure 1).real (Set.Iio s) = 1 - Real.exp (-s) := by
  rw [measureReal_def, measure_congr Iio_ae_eq_Iic, ← measureReal_def,
    ← cdf_eq_real, cdf_expMeasure_eq (by norm_num), if_pos hs]
  simp only [one_mul]
lemma expOne_real_Ici (s : ℝ) (hs : 0 ≤ s) :
    (expMeasure 1).real (Set.Ici s) = Real.exp (-s) := by
  rw [← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio, expOne_real_Iio s hs]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def retainedVertices (S : Finset V) (s : ℝ) (r : V → ℝ) : Finset V :=
  S.filter (fun v => r v < s)
omit [DecidableEq V] in
theorem measurableSet_retainedVertices_eq (S T : Finset V) (b : ℝ) :
    MeasurableSet {u : V → ℝ | retainedVertices S b u = T} := by
  have heq : {u : V → ℝ | retainedVertices S b u = T} =
      {u : V → ℝ | ∀ v, (v ∈ S ∧ u v < b) ↔ v ∈ T} := by
    ext u
    simp [Finset.ext_iff, retainedVertices]
  rw [heq]
  apply Measurable.setOf
  apply Measurable.forall
  intro v
  exact (measurable_const.and ((measurable_pi_apply v).lt measurable_const)).iff
    measurable_const

omit [Fintype V] [DecidableEq V] in
theorem measurable_retainedVertices_card (S : Finset V) (b : ℝ) :
    Measurable (fun u : V → ℝ => (retainedVertices S b u).card) := by
  have heq : (fun u : V → ℝ => (retainedVertices S b u).card) =
      fun u => ∑ v ∈ S, if u v < b then (1 : ℕ) else 0 := by
    funext u
    simp only [retainedVertices, Finset.card_filter]
  rw [heq]
  apply Finset.measurable_sum
  intro v _
  exact Measurable.ite ((measurable_pi_apply v).lt measurable_const).setOf
    measurable_const measurable_const

omit [Fintype V] in
theorem retainedVertices_eq_pi (S T : Finset V) (hTS : T ⊆ S) (b : ℝ) :
    {u : V → ℝ | retainedVertices S b u = T} =
      (S : Set V).pi (fun v => if v ∈ T then Set.Iio b else Set.Ici b) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
  constructor
  · intro heq v hv
    by_cases hvT : v ∈ T
    · have hmem : v ∈ retainedVertices S b u := heq.symm ▸ hvT
      simpa [hvT] using (Finset.mem_filter.mp hmem).2
    · simp only [hvT, ↓reduceIte, Set.mem_Ici]
      by_contra h
      exact hvT (heq ▸ Finset.mem_filter.mpr ⟨hv, lt_of_not_ge h⟩)
  · intro h
    apply Finset.ext
    intro v
    simp only [retainedVertices, Finset.mem_filter]
    constructor
    · rintro ⟨hvS, hvb⟩
      by_contra hvT
      have hge : b ≤ u v := by simpa [hvT] using h v hvS
      exact (not_lt_of_ge hge) hvb
    · intro hvT
      exact ⟨hTS hvT, by simpa [hvT] using h v (hTS hvT)⟩


theorem measure_retainedVertices_eq (S T : Finset V) (hTS : T ⊆ S)
    (s : ℝ) (hs : 0 ≤ s) :
    Measure.pi (fun _ : V => expMeasure 1) {u | retainedVertices S s u = T} =
      ENNReal.ofReal (1 - Real.exp (-s)) ^ T.card *
        ENNReal.ofReal (Real.exp (-s)) ^ (S.card - T.card) := by
  rw [retainedVertices_eq_pi S T hTS s, Measure.pi_pi_finset]
  have hlo : expMeasure 1 (Set.Iio s) = ENNReal.ofReal (1 - Real.exp (-s)) := by
    rw [← ofReal_measureReal, expOne_real_Iio s hs]
  have hhi : expMeasure 1 (Set.Ici s) = ENNReal.ofReal (Real.exp (-s)) := by
    rw [← ofReal_measureReal, expOne_real_Ici s hs]
  simp only [apply_ite,hlo,hhi]
  rw [Finset.prod_ite]
  have hfilter : S.filter (fun v => v ∈ T) = T := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨hTS hv,hv⟩⟩
  rw [hfilter, ← Finset.sdiff_eq_filter]
  simp [Finset.card_sdiff,Finset.inter_eq_left.mpr hTS]

theorem measureReal_retainedVertices_eq (S T : Finset V) (hTS : T ⊆ S)
    (s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi (fun _ : V => expMeasure 1)).real {u | retainedVertices S s u = T} =
      (1 - Real.exp (-s)) ^ T.card * Real.exp (-s) ^ (S.card - T.card) := by
  have hp : 0 ≤ 1 - Real.exp (-s) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [measureReal_def,measure_retainedVertices_eq S T hTS s hs,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal (Real.exp_pos _).le]
/-- The cardinality of the retained set has the binomial distribution. -/
theorem measureReal_retainedVertices_card (S : Finset V) (j : ℕ)
    (b : ℝ) (hb : 0 ≤ b) :
    (Measure.pi (fun _ : V => expMeasure 1)).real
      {u | (retainedVertices S b u).card = j} =
      (S.card.choose j : ℝ) * (1 - Real.exp (-b)) ^ j *
        Real.exp (-b) ^ (S.card - j) := by
  have heq : {u : V → ℝ | (retainedVertices S b u).card = j} =
      ⋃ T ∈ S.powersetCard j, {u | retainedVertices S b u = T} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard]
    constructor
    · intro hcard
      exact ⟨retainedVertices S b u, ⟨Finset.filter_subset _ _, hcard⟩, rfl⟩
    · rintro ⟨T, ⟨_, hT⟩, hEq⟩
      simpa [hEq] using hT
  rw [heq, measureReal_biUnion_finset]
  · calc
      _ = ∑ _T ∈ S.powersetCard j,
          (1 - Real.exp (-b)) ^ j *
            Real.exp (-b) ^ (S.card - j) := by
        apply Finset.sum_congr rfl
        intro T hT
        rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hcard⟩
        rw [measureReal_retainedVertices_eq S T hTS b hb, hcard]
      _ = _ := by simp [mul_assoc]
  · intro T _ U _ hTU
    apply Set.disjoint_left.mpr
    intro u huT huU
    exact hTU (huT.symm.trans huU)
  · intro T _
    exact measurableSet_retainedVertices_eq S T b


end ExponentialArrivals

-- Source: Solutions.ConditionalRankBand
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace ConditionalRankBand
open Classical ExponentialArrivals
variable {V : Type*} [Fintype V] [LinearOrder V]
noncomputable def marginal (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) (v : V) : Measure ℝ :=
  if r₀ v < θ then Measure.dirac (r₀ v) else if v∈A then Measure.dirac (rA v)
  else (expMeasure 1).map (fun x => θ+x)
instance marginal_probability (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) (v : V) :
    IsProbabilityMeasure (marginal r₀ θ A rA v) := by
  unfold marginal
  split_ifs
  · infer_instance
  · infer_instance
  · exact Measure.isProbabilityMeasure_map (by fun_prop)
def band (a : ℝ) (b : WithTop ℝ) : Set ℝ := {x | a ≤ x ∧ (x:WithTop ℝ)<b}
lemma band_measurable (a : ℝ) (b : WithTop ℝ) : MeasurableSet (band a b) := by
  induction b using WithTop.recTopCoe with
  | top =>
    convert (measurableSet_Ici : MeasurableSet (Set.Ici a)) using 1
    ext x; simp only [band,Set.mem_setOf_eq,WithTop.coe_lt_top, and_true,Set.mem_Ici]
  | coe b =>
    convert (measurableSet_Ico : MeasurableSet (Set.Ico a b)) using 1
    ext x; simp only [band,Set.mem_setOf_eq,WithTop.coe_lt_coe,Set.mem_Ico]
lemma exp_tail (s : ℝ) (hs : 0 ≤ s) : expMeasure 1 (Set.Ici s) = ENNReal.ofReal (Real.exp (-s)) := by
  rw [← ofReal_measureReal,expOne_real_Ici s hs]
lemma exp_band (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    expMeasure 1 (Set.Ico s t) = ENNReal.ofReal (1-Real.exp (-(t-s))) * expMeasure 1 (Set.Ici s) := by
  have hdiff : Set.Ici s \ Set.Ici t = Set.Ico s t := by ext x; simp
  rw [← hdiff,measure_sdiff (Set.Ici_subset_Ici.mpr hst) measurableSet_Ici.nullMeasurableSet (measure_ne_top _ _),
    exp_tail s hs,exp_tail t (hs.trans hst),← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))]
  congr 1
  rw [sub_mul,one_mul,←Real.exp_add]
  congr 2
  ring
lemma marginal_band (r₀ : V → ℝ) (θ a : ℝ) (hθa : θ < a) (A : Finset V) (rA : V → ℝ)
    (v : V) (hv : v∉A) (b : WithTop ℝ) (hab : (a:WithTop ℝ)<b) :
    marginal r₀ θ A rA v (band a b) =
      ENNReal.ofReal (oneMinusExp a b) * marginal r₀ θ A rA v (Set.Ici a) := by
  by_cases he : r₀ v < θ
  · have hr : r₀ v < a := he.trans hθa
    simp [marginal,he,band,not_le.mpr hr]
  · simp only [marginal,if_neg he,if_neg hv]
    rw [Measure.map_apply (by fun_prop) (band_measurable a b),Measure.map_apply (by fun_prop) measurableSet_Ici]
    have ht : (fun x : ℝ => θ+x) ⁻¹' Set.Ici a = Set.Ici (a-θ) := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Ici]
      constructor <;> intro h <;> linarith
    rw [ht]
    induction b using WithTop.recTopCoe with
    | top =>
      simp only [band,WithTop.coe_lt_top,and_true,oneMinusExp,↓reduceDIte,ENNReal.ofReal_one,one_mul]
      congr 1
    | coe b =>
      have hb : a < b := WithTop.coe_lt_coe.mp hab
      have hi : (fun x : ℝ => θ+x) ⁻¹' band a (b:WithTop ℝ) = Set.Ico (a-θ) (b-θ) := by
        ext x
        simp only [Set.mem_preimage,band,Set.mem_setOf_eq,WithTop.coe_lt_coe,Set.mem_Ico]
        constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
      rw [hi,exp_band (a-θ) (b-θ) (by linarith) (by linarith)]
      simp only [oneMinusExp,WithTop.coe_ne_top,↓reduceDIte,WithTop.untop_coe]
      rw [show b-θ-(a-θ) = b-a by ring]
end ConditionalRankBand

-- Source: Solutions.ExponentialMemoryless
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ExponentialMemoryless
open ExponentialArrivals ConditionalRankBand
lemma tail_all (s : ℝ) : expMeasure 1 (Set.Ici s) = ENNReal.ofReal (Real.exp (-max s 0)) := by
  by_cases hs : 0 ≤ (s : ℝ)
  · rw [max_eq_left hs,exp_tail s hs]
  · have hs : s ≤ 0 := le_of_not_ge hs
    rw [max_eq_right hs,neg_zero,Real.exp_zero,ENNReal.ofReal_one]
    apply le_antisymm prob_le_one
    have hh := measure_mono (Set.Ici_subset_Ici.mpr hs) (μ:=expMeasure 1)
    simpa [exp_tail 0 le_rfl] using hh
noncomputable def shifted (θ : ℝ) : Measure ℝ := (expMeasure 1).map (fun x=>θ+x)
instance shifted_probability (θ : ℝ) : IsProbabilityMeasure (shifted θ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)
lemma shifted_tail (θ s : ℝ) : shifted θ (Set.Ici s) = ENNReal.ofReal (Real.exp (-max (s-θ) 0)) := by
  rw [shifted,Measure.map_apply (by fun_prop) measurableSet_Ici]
  have he : (fun x : ℝ=>θ+x) ⁻¹' Set.Ici s = Set.Ici (s-θ) := by
    ext x; simp only [Set.mem_preimage,Set.mem_Ici]; constructor <;> intro h <;> linarith
  rw [he,tail_all]
lemma restrict_shifted (θ a : ℝ) (ha : θ ≤ a) :
    (shifted θ).restrict (Set.Ici a) = ENNReal.ofReal (Real.exp (-(a-θ))) • shifted a := by
  apply Measure.ext_of_Ici
  intro t
  rw [Measure.restrict_apply measurableSet_Ici,Set.Ici_inter_Ici,shifted_tail,
    Measure.smul_apply,smul_eq_mul,shifted_tail,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  by_cases ht : a ≤ t
  · rw [max_eq_left ht,max_eq_left (by linarith : 0 ≤ t-θ),max_eq_left (by linarith : 0 ≤ t-a)]
    ring
  · have ht : t ≤ a := le_of_not_ge ht
    rw [max_eq_right ht,max_eq_left (by linarith : 0 ≤ a-θ),max_eq_right (by linarith : t-a ≤ 0)]
    ring
end ExponentialMemoryless

-- Source: Solutions.GammaEstimate
open MeasureTheory ProbabilityTheory RGMISFast
set_option autoImplicit false

lemma exp_one_ae_nonnegative : ∀ᵐ x ∂(expMeasure 1), 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change (expMeasure 1) (Set.Iio 0) = 0
  rw [show expMeasure 1 = volume.withDensity (gammaPDF 1 1) from rfl,
    withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma exp_one_integrable_exp {f : ℝ → ℝ} (hf : Measurable f)
    (hneg : ∀ᵐ x ∂(expMeasure 1), f x ≤ 0) :
    Integrable (fun x => Real.exp (f x)) (expMeasure 1) := by
  letI := isProbabilityMeasure_expMeasure (r := (1:ℝ)) (by norm_num)
  apply (integrable_const (1:ℝ)).mono' (hf.exp.aestronglyMeasurable)
  filter_upwards [hneg] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_one_iff.mpr hx

lemma exp_one_laplace (a : ℝ) (ha : 0 < a) :
    (∫ x, Real.exp (-2*x/a) ∂(expMeasure 1)) = a/(a+2) := by
  change (∫ x, Real.exp (-2*x/a) ∂volume.withDensity (exponentialPDF 1)) = _
  have hmeas : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hmeas
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have he : (fun x : ℝ => (exponentialPDF 1 x).toReal • Real.exp (-2*x/a)) =
      (Set.Ici (0:ℝ)).indicator (fun x => Real.exp ((-(1+2/a))*x)) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [exponentialPDF_eq,if_pos hx,one_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,
        smul_eq_mul,Set.indicator_of_mem (show x ∈ Set.Ici (0:ℝ) from hx)]
      rw [← Real.exp_add]
      congr 1; ring
    · simp [exponentialPDF_eq,hx,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
  have hn : -(1+2/a) < 0 := by
    have hp : 0 < 2/a := by positivity
    linarith
  rw [integral_exp_mul_Ioi hn 0]
  simp only [mul_zero,Real.exp_zero]
  have hp : a+2 ≠ 0 := by linarith
  field_simp
  <;> ring

lemma exponential_reciprocal_bound (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.exp (-2/x) ≤ x*Real.exp (-2) := by
  have hi : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hl
  have he : Real.exp (2-2/x) ≤ x := by
    calc
      _ ≤ Real.exp (Real.log x) := by
        apply Real.exp_le_exp.mpr
        simp only [div_eq_mul_inv]
        linarith
      _ = x := Real.exp_log hx
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-2)).le
  rw [← Real.exp_add] at hm
  convert hm using 1 <;> congr 1 <;> ring

lemma gammaA_split_bound (a : ℝ) (ha : 0 < a) :
    gammaA a ≤ Real.exp (-2)*(∫ x,Real.exp (-2*x/a) ∂(expMeasure 1)) + Real.exp (-2*a0/a) := by
  letI := isProbabilityMeasure_expMeasure (r := (1:ℝ)) (by norm_num)
  have ha0 : 0 < a0 := Real.exp_pos 2
  have hi : Integrable (fun x:ℝ => Real.exp (-2*x/a)) (expMeasure 1) := by
    apply exp_one_integrable_exp (by fun_prop)
    filter_upwards [exp_one_ae_nonnegative] with x hx
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le
  have hg : Integrable (fun x:ℝ => Real.exp (-2*min (a+x) a0/a)) (expMeasure 1) := by
    apply exp_one_integrable_exp (by fun_prop)
    filter_upwards [exp_one_ae_nonnegative] with x hx
    have hmin : 0 ≤ min (a+x) a0 := le_min (by linarith) ha0.le
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le
  have hb : ∀x:ℝ, Real.exp (-2*min (a+x) a0/a) ≤
      Real.exp (-2)*Real.exp (-2*x/a)+Real.exp (-2*a0/a) := by
    intro x
    by_cases hx : a+x ≤ a0
    · rw [min_eq_left hx,←Real.exp_add]
      have he : -2*(a+x)/a = -2 + -2*x/a := by field_simp; ring
      rw [he]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [min_eq_right (le_of_not_ge hx)]
      exact le_add_of_nonneg_left (by positivity)
  have hmono := integral_mono hg ((hi.const_mul (Real.exp (-2))).add (integrable_const _)) hb
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hi.const_mul _) (integrable_const _),integral_const_mul] at hmono
  simpa [gammaA] using hmono

lemma gammaA_scalar_bound (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) ≤ a*Real.exp (-2)*(1/2+1/a0) := by
  have hp : 0 < a0 := Real.exp_pos 2
  have hx := exponential_reciprocal_bound (a/a0) (div_pos ha hp) ((div_le_one hp).mpr ha0)
  have he : -2/(a/a0) = -2*a0/a := by field_simp
  rw [he] at hx
  have hfrac := div_le_div_of_nonneg_left (show 0 ≤ a*Real.exp (-2) by positivity)
    (by norm_num : (0:ℝ)<2) (show 2 ≤ a+2 by linarith)
  calc
    _ ≤ a*Real.exp (-2)/2+(a/a0)*Real.exp (-2) := add_le_add hfrac hx
    _ = _ := by ring

lemma gammaA_ratio_bound (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    2*Real.exp 1*gammaA a/a ≤ Real.exp (-1)+2*Real.exp (-3) := by
  have hg := gammaA_split_bound a ha
  rw [exp_one_laplace a ha] at hg
  have hb := gammaA_scalar_bound a ha ha0
  have hgamma : gammaA a ≤ a*Real.exp (-2)*(1/2+1/a0) := by
    calc
      _ ≤ _ := hg
      _ = a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) := by ring
      _ ≤ _ := hb
  have hh := mul_le_mul_of_nonneg_left hgamma (show 0 ≤ 2*Real.exp 1/a by positivity)
  have he2 : Real.exp 2 = (Real.exp 1)^2 := by rw [←Real.exp_nat_mul]; norm_num
  have he3 : Real.exp 3 = (Real.exp 1)^3 := by rw [←Real.exp_nat_mul]; norm_num
  have he : (2*Real.exp 1/a)*(a*Real.exp (-2)*(1/2+1/a0)) =
      Real.exp (-1)+2*Real.exp (-3) := by
    unfold a0
    simp only [Real.exp_neg,he2,he3]
    have hene : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
    field_simp
    <;> ring
  rw [he] at hh
  calc
    _ = (2*Real.exp 1/a)*gammaA a := by ring
    _ ≤ _ := hh

lemma gammaA_ratio_lt_half : Real.exp (-1)+2*Real.exp (-3) < (1/2:ℝ) := by
  have h := Real.exp_one_gt_d9
  have hp := Real.exp_pos 1
  have hbound : (27/10:ℝ) < Real.exp 1 := by linarith
  have he3 : Real.exp 3 = (Real.exp 1)^3 := by rw [←Real.exp_nat_mul]; norm_num
  simp only [Real.exp_neg,he3]
  have hi : (Real.exp 1)⁻¹ ≤ (10/27:ℝ) := by
    apply (inv_le_comm₀ hp (by norm_num)).mpr
    norm_num
    linarith
  have hi3 : ((Real.exp 1)⁻¹)^3 ≤ (10/27:ℝ)^3 := pow_le_pow_left₀ (by positivity) hi _
  rw [← inv_pow]

  nlinarith

theorem eq28_complete (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    gammaA a ≤ Real.exp (-2) * (∫ x, Real.exp (-2*x/a) ∂(expMeasure 1)) + Real.exp (-2*a0/a) ∧
    Real.exp (-2) * (∫ x, Real.exp (-2*x/a) ∂(expMeasure 1)) + Real.exp (-2*a0/a) =
      a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) ∧
    a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) ≤ a*Real.exp (-2)*(1/2+1/a0) ∧
    (∀x:ℝ,0 < x → x ≤ 1 → Real.exp (-2/x) ≤ x*Real.exp (-2)) ∧
    2*Real.exp 1*gammaA a/a ≤ Real.exp (-1)+2*Real.exp (-3) ∧
    Real.exp (-1)+2*Real.exp (-3)<1/2 := by
  refine ⟨gammaA_split_bound a ha,?_,gammaA_scalar_bound a ha ha0,
    exponential_reciprocal_bound,gammaA_ratio_bound a ha ha0,gammaA_ratio_lt_half⟩
  rw [exp_one_laplace a ha]
  ring

-- Source: Solutions.RankChargeLaplaceComplete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace RankChargeLaplace
open Classical ExponentialArrivals ConditionalRankBand ExponentialMemoryless
variable {V : Type*} [Fintype V] [LinearOrder V]
noncomputable def kernel (a : ℝ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2*min x a0/a))
lemma kernel_measurable (a : ℝ) : Measurable (kernel a) := by unfold kernel; fun_prop
lemma gamma_integrable (a : ℝ) (ha : 0<a) :
    Integrable (fun x=>Real.exp (-2*min (a+x) a0/a)) (expMeasure 1) := by
  apply exp_one_integrable_exp (by fun_prop)
  filter_upwards [exp_one_ae_nonnegative] with x hx
  apply div_nonpos_of_nonpos_of_nonneg _ ha.le
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_min (by linarith) (Real.exp_pos 2).le)
lemma kernel_gamma (a : ℝ) (ha : 0<a) :
    (∫⁻x,kernel a x ∂shifted a) = ENNReal.ofReal (gammaA a) := by
  rw [shifted,lintegral_map (kernel_measurable a) (by fun_prop)]
  exact (ofReal_integral_eq_lintegral_ofReal (gamma_integrable a ha)
    (Filter.Eventually.of_forall (fun x=>(Real.exp_pos _).le))).symm
lemma marginal_kernel (r₀ : V→ℝ) (θ a : ℝ) (ha : 0<a) (hθa : θ<a) (v : V) :
    (∫⁻x in Set.Ici a,kernel a x ∂marginal r₀ θ ∅ (fun _=>0) v) =
      marginal r₀ θ ∅ (fun _=>0) v (Set.Ici a) * ENNReal.ofReal (gammaA a) := by
  by_cases he : r₀ v<θ
  · have hn : r₀ v∉Set.Ici a := not_le.mpr (he.trans hθa)
    simp [marginal,he,restrict_dirac,hn]
  · simp only [marginal,if_neg he,Finset.notMem_empty,↓reduceIte]
    change (∫⁻x,kernel a x ∂(shifted θ).restrict (Set.Ici a)) = shifted θ (Set.Ici a)*_
    rw [restrict_shifted θ a hθa.le,lintegral_smul_measure,kernel_gamma a ha,
      shifted_tail,max_eq_left (sub_nonneg.mpr hθa.le)]
    rfl
lemma exponential_product (r : V→ℝ) (A : Finset V) (a L : ℝ) :
    ENNReal.ofReal (Real.exp (-(2*S r A a+L))) = ENNReal.ofReal (Real.exp (-L))*∏v∈A,kernel a (r v) := by
  have he : -(2*S r A a+L) = -L+∑v∈A,(-2*min (r v) a0/a) := by
    unfold S rbar
    rw [← Finset.sum_div,← Finset.mul_sum]
    ring
  rw [he,Real.exp_add,Real.exp_sum,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_prod_of_nonneg (fun _ _=>(Real.exp_pos _).le)]
  rfl
lemma high_measurable (A : Finset V) (a : ℝ) : MeasurableSet {r : V→ℝ|∀v∈A,a ≤ r v} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun v=>MeasurableSet.iInter (fun _=>measurableSet_le measurable_const (measurable_pi_apply v)))
end RankChargeLaplace
open Classical RankChargeLaplace ConditionalRankBand ExponentialArrivals
 theorem conditional_rank_charge_laplace_complete {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ a L : ℝ) (ha : 0 < a) (hθa : θ < a) (A : Finset V) :
    (∫⁻ r in {r | ∀ v ∈ A, a ≤ r v},
      ENNReal.ofReal (Real.exp (-(2 * S r A a + L))) ∂(condLaw r₀ θ ∅ (fun _ => 0))) =
      condLaw r₀ θ ∅ (fun _ => 0) {r | ∀ v ∈ A, a ≤ r v} *
        ENNReal.ofReal (Real.exp (-L) * gammaA a ^ A.card) := by
  let μ := marginal r₀ θ ∅ (fun _=>0)
  let f : ℝ→ℝ≥0∞ := (Set.Ici a).indicator (kernel a)
  have hf : Measurable f := (kernel_measurable a).indicator measurableSet_Ici
  have he (r : V→ℝ) : {r : V→ℝ|∀v∈A,a ≤ r v}.indicator
      (fun r=>ENNReal.ofReal (Real.exp (-(2*S r A a+L)))) r =
      ENNReal.ofReal (Real.exp (-L))*∏v∈A,f (r v) := by
    by_cases hr : ∀v∈A,a ≤ r v
    · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_pos hr]
      rw [exponential_product]
      congr 1
      apply Finset.prod_congr rfl
      intro v hv
      exact (Set.indicator_of_mem (hr v hv) (kernel a)).symm
    · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg hr]
      obtain ⟨v,hv⟩ := not_forall.mp hr
      obtain ⟨hv,hva⟩ := _root_.not_imp.mp hv
      have hz : ∏w∈A,f (r w) = 0 := Finset.prod_eq_zero hv (Set.indicator_of_notMem hva (kernel a))
      rw [hz,mul_zero]
  have hind : iIndepFun (fun v (r : V→ℝ)=>f (r v)) (Measure.pi μ) := iIndepFun_pi (fun _=>hf.aemeasurable)
  have hi (v : V) : (∫⁻r,f (r v) ∂Measure.pi μ) = μ v (Set.Ici a)*ENNReal.ofReal (gammaA a) := by
    rw [← lintegral_map hf (measurable_pi_apply v),(measurePreserving_eval μ v).map_eq]
    rw [show f=(Set.Ici a).indicator (kernel a) from rfl,lintegral_indicator measurableSet_Ici]
    exact marginal_kernel r₀ θ a ha hθa v
  have hp : condLaw r₀ θ ∅ (fun _=>0) {r|∀v∈A,a ≤ r v} = ∏v∈A, μ v (Set.Ici a) := by
    change Measure.pi μ _ = _
    have he : {r : V→ℝ|∀v∈A,a ≤ r v} = (A:Set V).pi (fun _=>Set.Ici a) := by ext r; simp
    rw [he,Measure.pi_pi_finset]
  rw [← lintegral_indicator (high_measurable A a)]
  simp_rw [he]
  change (∫⁻r,ENNReal.ofReal (Real.exp (-L))*∏v∈A,f (r v) ∂Measure.pi μ) = _
  have hmprod : Measurable (fun r : V→ℝ=>∏v∈A,f (r v)) := Finset.measurable_prod _ (fun v _=>hf.comp (measurable_pi_apply v))
  rw [lintegral_const_mul _ hmprod,
    lintegral_prod_eq_prod_lintegral_of_indepFun A _ hind (fun v=>hf.comp (measurable_pi_apply v))]
  simp_rw [hi]
  rw [Finset.prod_mul_distrib,Finset.prod_const,hp,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_pow (show 0 ≤ gammaA a from integral_nonneg (fun x=>(Real.exp_pos _).le))]
  ac_rfl

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ a L : ℝ) (ha : 0 < a) (hθa : θ < a) (A : Finset V) :
    (∫⁻ r in {r | ∀ v ∈ A, a ≤ r v},
      ENNReal.ofReal (Real.exp (-(2 * S r A a + L))) ∂(condLaw r₀ θ ∅ (fun _ => 0))) =
      condLaw r₀ θ ∅ (fun _ => 0) {r | ∀ v ∈ A, a ≤ r v} *
        ENNReal.ofReal (Real.exp (-L) * gammaA a ^ A.card) := by
  exact conditional_rank_charge_laplace_complete r₀ θ a L ha hθa A

#print axioms solution
