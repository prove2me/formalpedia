-- Prove2me | solution 2 for RGMISFast.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T04:44:24.904052+00:00
-- url     : https://prove2.me/submissions/9bae4cfd-1bd4-4f74-b368-57038471fa09

import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_IsRootConnected
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw
import Definitions.Def_RGMISFast_gammaA
import Mathlib
set_option maxHeartbeats 1000000

-- Source: Solutions.CoordinateDisintegration
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CoordinateDisintegration
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def overlay (A : Finset V) (p : (V→ℝ) × (V→ℝ)) : V→ℝ :=
  fun v=>if v∈A then p.1 v else p.2 v
lemma overlay_measurable (A : Finset V) : Measurable (overlay A) := by
  apply measurable_pi_lambda
  intro v
  unfold overlay
  split_ifs <;> fun_prop
lemma overlay_map (μ : V→Measure ℝ) [∀v,IsProbabilityMeasure (μ v)] (A : Finset V) :
    ((Measure.pi μ).prod (Measure.pi μ)).map (overlay A) = Measure.pi μ := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ V
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ V μ μ).map_eq
  rw [← he,Measure.map_map (overlay_measurable A) e.measurable]
  change (Measure.pi (fun v=>(μ v).prod (μ v))).map
    (fun r v=>if v∈A then (r v).1 else (r v).2) = _
  rw [Measure.pi_map_pi (fun v=>show AEMeasurable (fun p : ℝ×ℝ=>if v∈A then p.1 else p.2) ((μ v).prod (μ v)) from by
    by_cases hv : v∈A <;> simp only [hv,↓reduceIte] <;> fun_prop)]
  congr 1
  funext v
  by_cases hv : v∈A <;> simp [hv]
lemma integral_overlay (μ : V→Measure ℝ) [∀v,IsProbabilityMeasure (μ v)] (A : Finset V)
    (f : (V→ℝ)→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻r,f r ∂Measure.pi μ) = ∫⁻r,∫⁻q,f (overlay A (r,q)) ∂Measure.pi μ ∂Measure.pi μ := by
  calc
    _ = ∫⁻r,f r ∂((Measure.pi μ).prod (Measure.pi μ)).map (overlay A) := by rw [overlay_map]
    _ = _ := by
      rw [lintegral_map hf (overlay_measurable A)]
      exact lintegral_prod _ (hf.comp (overlay_measurable A)).aemeasurable
end CoordinateDisintegration

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

-- Source: Solutions.CountMeasurability
open RGMISFast MeasureTheory
set_option autoImplicit false

lemma mis_true_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    inMIS G r v = true ↔ ∀ w, G.Adj v w → r w < r v → inMIS G r w = false := by
  rw [inMIS_eq]
  simp only [List.all_eq_true]
  constructor
  · intro h w ha hr
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h ⟨w,(mem_lowerNbrs G r).mpr ⟨ha,hr⟩⟩ (by simp)
  · intro h w hw
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h w.val ((mem_lowerNbrs G r).mp w.property).1 ((mem_lowerNbrs G r).mp w.property).2

lemma mis_order_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V → ℝ)
    (hord : ∀ v w, r v < r w ↔ s v < s w) (v : V) : inMIS G r v = inMIS G s v := by
  induction v using (measure (rk r)).wf.induction with
  | h v ih =>
    have he : inMIS G r v = true ↔ inMIS G s v = true := by
      rw [mis_true_iff,mis_true_iff]
      constructor
      · intro h w ha hw
        rw [← ih w (rk_lt r ((hord w v).mpr hw))]
        exact h w ha ((hord w v).mpr hw)
      · intro h w ha hw
        rw [ih w (rk_lt r hw)]
        exact h w ha ((hord w v).mp hw)
    cases hr : inMIS G r v <;> cases hs : inMIS G s v <;> simp_all

lemma mis_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Measurable (fun r : V → ℝ => inMIS G r v) := by
  classical
  let code : (V → ℝ) → (V → V → Prop) := fun r a b => r a < r b
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    exact measurableSet_setOf.mp (measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b))
  have hf : (fun r : V → ℝ => inMIS G r v).FactorsThrough code := by
    intro r s he
    apply mis_order_congr G r s
    intro a b
    exact iff_of_eq (congrFun (congrFun he a) b)
  obtain ⟨f,he⟩ := (Function.factorsThrough_iff _).mp hf
  rw [he]
  exact (measurable_of_countable f).comp hm

lemma active_vertex_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (t : ℝ) (v : V) :
    t ≤ tau G r v ↔ ∀ w, (w = v ∨ G.Adj v w) → inMIS G r w = true → t ≤ r w := by
  classical
  unfold tau
  rw [Finset.le_min'_iff]
  constructor
  · intro h w hw hm
    exact h (r w) (Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr
      ⟨by simpa using hw,hm⟩,rfl⟩)
  · intro h y hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw,hm⟩ := Finset.mem_filter.mp hw
    exact h w (by simpa using hw) hm

lemma active_vertex_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (v : V) :
    MeasurableSet {r : V → ℝ | t ≤ tau G r v} := by
  simp only [active_vertex_iff, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro w
  apply MeasurableSet.iInter
  intro hw
  have hm := mis_measurable G w
  have hb : MeasurableSet {r : V → ℝ | inMIS G r w = true} := measurableSet_eq_fun hm measurable_const
  have ht : MeasurableSet {r : V → ℝ | t ≤ r w} := measurableSet_le measurable_const (measurable_pi_apply w)
  convert hb.compl.union ht using 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]

lemma measurable_of_activity {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (f : (V → ℝ) → ℕ)
    (hf : ∀ r s, (∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) → f r = f s) : Measurable f := by
  classical
  let code : (V → ℝ) → (V → Prop) := fun r v => t ≤ tau G r v
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro v
    exact measurableSet_setOf.mp (active_vertex_measurable G t v)
  have hfac : f.FactorsThrough code := by
    intro r s he
    exact hf r s (fun v => iff_of_eq (congrFun he v))
  obtain ⟨g,he⟩ := (Function.factorsThrough_iff _).mp hfac
  rw [he]
  exact (measurable_of_countable g).comp hm

lemma activeAt_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (r s : V → ℝ)
    (h : ∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) (A : Finset V) :
    ActiveAt G r t A = ActiveAt G s t A := by
  unfold ActiveAt
  simp_rw [h]

lemma Ncount_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Ncount G A k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Ncount
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma Y_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Y G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma dsSum_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => dsSum G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  have he : {x | t ≤ tau G r x} = {x | t ≤ tau G s x} := Set.ext h
  have hc : countedW G u k t r = countedW G u k t s := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    rw [activeAt_congr G t r s h]
  unfold dsSum
  rw [he,hc]

-- Source: Solutions.PinnedActivity
open RGMISFast
namespace PinnedActivity
variable {V : Type*} [Fintype V] [LinearOrder V]

lemma activity_prefix_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s : ℝ)
    (hlow : ∀ v, r v < s ↔ q v < s)
    (heq : ∀ v, r v < s → r v = q v) (v : V) :
    s ≤ tau G r v ↔ s ≤ tau G q v := by
  have hm : ∀ w, r w < s → inMIS G r w = inMIS G q w := by
    intro w
    induction w using (measure (rk r)).wf.induction with
    | h w ih =>
      intro hw
      have hew := heq w hw
      have hh : inMIS G r w = true ↔ inMIS G q w = true := by
        rw [mis_true_iff,mis_true_iff]
        constructor
        · intro h z ha hz
          have hzs : q z < s := hz.trans (hew ▸ hw)
          have hzr := (hlow z).mpr hzs
          have hzw : r z < r w := by simpa only [heq z hzr, hew] using hz
          rw [← ih z (rk_lt r hzw) hzr]
          exact h z ha hzw
        · intro h z ha hz
          have hzs := hz.trans hw
          rw [ih z (rk_lt r hz) hzs]
          exact h z ha (by simpa only [← heq z hzs, ← hew] using hz)
      cases hr : inMIS G r w <;> cases hq : inMIS G q w <;> simp_all
  rw [active_vertex_iff,active_vertex_iff]
  constructor
  · intro h w ha hqw
    by_contra hs
    have hwr := (hlow w).mpr (lt_of_not_ge hs)
    have hrw : inMIS G r w = true := (hm w hwr).trans hqw
    exact (not_le_of_gt hwr) (h w ha hrw)
  · intro h w ha hrw
    by_contra hs
    have hwr := lt_of_not_ge hs
    have hqw : inMIS G q w = true := (hm w hwr).symm.trans hrw
    exact (not_le_of_gt ((hlow w).mp hwr)) (h w ha hqw)

/-- Ranks already at least s can be pinned to arbitrary other values at least s
without changing any vertex's activity at s. -/
theorem pinning_above_threshold
    (G : SimpleGraph V) [DecidableRel G.Adj] (r a : V → ℝ) (s : ℝ) (A : Finset V)
    (hr : ∀ v ∈ A, s ≤ r v) (ha : ∀ v ∈ A, s ≤ a v) (v : V) :
    s ≤ tau G r v ↔ s ≤ tau G (fun w => if w ∈ A then a w else r w) v := by
  classical
  apply activity_prefix_congr
  · intro w
    by_cases hw : w ∈ A
    · simp only [if_pos hw]
      exact iff_of_false (not_lt_of_ge (hr w hw)) (not_lt_of_ge (ha w hw))
    · simp only [if_neg hw]
  · intro w hw
    have hn : w ∉ A := fun h => (not_lt_of_ge (hr w h)) hw
    simp only [if_neg hn]
end PinnedActivity

-- Source: Solutions.SingleArrival
open RGMISFast
namespace SingleArrival
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ)

/-- Across an interval with exactly one possible arriving vertex, only that
vertex's selection can change activity. -/
lemma activity_transition (s t : ℝ) (hst : s ≤ t) (x v : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    t ≤ tau G r v ↔ s ≤ tau G r v ∧
      (inMIS G r x = true → v ≠ x ∧ ¬ G.Adj v x) := by
  constructor
  · intro ht
    refine ⟨hst.trans ht, ?_⟩
    intro hm
    have h := (active_vertex_iff G r t v).mp ht
    constructor
    · intro he
      subst v
      exact (not_le_of_gt hx.2) (h x (Or.inl rfl) hm)
    · intro ha
      exact (not_le_of_gt hx.2) (h x (Or.inr ha) hm)
  · rintro ⟨hs, hsafe⟩
    apply (active_vertex_iff G r t v).mpr
    intro w hw hm
    have hsw := (active_vertex_iff G r s v).mp hs w hw hm
    by_contra htw
    have hwx := hone w hsw (lt_of_not_ge htw)
    subst w
    rcases hw with he | ha
    · exact (hsafe hm).1 he.symm
    · exact (hsafe hm).2 ha

/-- The unique arrival is selected exactly when it is still active at the
start of the interval. -/
lemma arrival_selected_iff (s t : ℝ) (x : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    inMIS G r x = true ↔ s ≤ tau G r x := by
  constructor
  · intro hm
    apply (active_vertex_iff G r s x).mpr
    intro w hw hwm
    rcases hw with he | ha
    · simpa only [he] using hx.1
    · by_contra hws
      have hl : r w < r x := (lt_of_not_ge hws).trans_le hx.1
      have hf := (mis_true_iff G r x).mp hm w ha hl
      simp_all
  · intro hs
    apply (mis_true_iff G r x).mpr
    intro w ha hw
    cases hm : inMIS G r w with
    | false => rfl
    | true =>
      have hsw := (active_vertex_iff G r s x).mp hs w (Or.inr ha) hm
      have he := hone w hsw (hw.trans hx.2)
      subst w
      exact False.elim (lt_irrefl _ hw)

lemma active_transition (s t : ℝ) (hst : s ≤ t) (x v : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    t ≤ tau G r v ↔ s ≤ tau G r v ∧
      (s ≤ tau G r x → v ≠ x ∧ ¬ G.Adj v x) := by
  rw [activity_transition G r s t hst x v hx hone, ← arrival_selected_iff G r s t x hx hone]
end SingleArrival

namespace SingleArrival
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ)
lemma active_set_transition (s t : ℝ) (hst : s ≤ t) (x : V) (A : Finset V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    ActiveAt G r t A ↔ ActiveAt G r s A ∧
      (s ≤ tau G r x → ∀ v ∈ A, v ≠ x ∧ ¬ G.Adj v x) := by
  constructor
  · intro h
    constructor
    · intro v hv
      exact hst.trans (h v hv)
    · intro hxa v hv
      exact ((active_transition G r s t hst x v hx hone).mp (h v hv)).2 hxa
  · rintro ⟨h,hkeep⟩ v hv
    exact (active_transition G r s t hst x v hx hone).mpr ⟨h v hv,fun hxa => hkeep hxa v hv⟩
end SingleArrival

-- Source: Solutions.RootCountCorrespondence
open RGMISFast
set_option autoImplicit false

lemma singleton_attached_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) (W : Finset V) :
    IsAttached G {u} W ↔ u ∉ W ∧ IsRootConnected G u (insert u W) := by
  classical
  constructor
  · rintro ⟨hd,hr⟩
    have hu : u ∉ W := by simpa using hd
    refine ⟨hu,Finset.mem_insert_self _ _,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact .refl _
    · obtain ⟨y,hy,hyx⟩ := hr x hx
      have he : y = u := Finset.mem_singleton.mp hy
      subst y
      simpa using hyx
  · rintro ⟨hu,hroot⟩
    refine ⟨by simpa using hu,?_⟩
    intro w hw
    exact ⟨u,Finset.mem_singleton_self _,by simpa using hroot.2 w (Finset.mem_insert_of_mem hw)⟩

lemma Y_eq_Ncount_singleton {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) (r : V → ℝ) :
    Y G u k t r = Ncount G {u} k t r := by
  classical
  unfold Y Ncount
  symm
  apply Finset.card_bij (fun W _ => insert u W)
  · intro W hW
    obtain ⟨_,hc,ha,ht⟩ := Finset.mem_filter.mp hW
    obtain ⟨hu,hr⟩ := (singleton_attached_iff G u W).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hr,?_,by simpa using ht⟩
    rw [Finset.card_insert_of_notMem hu,hc]
  · intro W hW Z hZ he
    have huW := ((singleton_attached_iff G u W).mp (Finset.mem_filter.mp hW).2.2.1).1
    have huZ := ((singleton_attached_iff G u Z).mp (Finset.mem_filter.mp hZ).2.2.1).1
    have hh := congrArg (fun A : Finset V => A.erase u) he
    simpa [Finset.erase_insert,Finset.erase_eq_of_notMem huW,Finset.erase_eq_of_notMem huZ] using hh
  · intro B hB
    obtain ⟨_,hr,hcard,ht⟩ := Finset.mem_filter.mp hB
    have he : insert u (B.erase u) = B := Finset.insert_erase hr.1
    refine ⟨B.erase u,?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_,?_⟩
    · rw [Finset.card_erase_of_mem hr.1,hcard]
      omega
    · apply (singleton_attached_iff G u _).mpr
      exact ⟨Finset.notMem_erase _ _,by simpa only [he] using hr⟩
    · simpa [he] using ht

-- Source: Solutions.ArrivalAuxiliary
open RGMISFast
namespace ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma active_le_rank (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (s : ℝ) (v : V)
    (hv : s ≤ tau G r v) : s ≤ r v := by
  by_contra hvs
  have hlt := lt_of_not_ge hvs
  have hm : inMIS G r v = true := by
    apply (mis_true_iff G r v).mpr
    intro w ha hw
    cases he : inMIS G r w with
    | false => rfl
    | true =>
      have hs := (active_vertex_iff G r s v).mp hv w (Or.inr ha) he
      exact False.elim ((not_le_of_gt (hw.trans hlt)) hs)
  exact (not_le_of_gt hlt) ((active_vertex_iff G r s v).mp hv v (Or.inl rfl) hm)
lemma activity_no_arrival (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hn : ∀ w, ¬ (s ≤ r w ∧ r w < t)) (v : V) :
    s ≤ tau G r v ↔ t ≤ tau G r v := by
  constructor
  · intro h
    apply (active_vertex_iff G r t v).mpr
    intro w hw hm
    have hs := (active_vertex_iff G r s v).mp h w hw hm
    exact le_of_not_gt (fun ht => hn w ⟨hs,ht⟩)
  · exact fun h => hst.trans h
lemma Y_eq_countedW (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) : Y G u k s r = (countedW G u k s r).card := by
  classical
  rw [Y_eq_Ncount_singleton]
  unfold Ncount countedW
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [singleton_attached_iff]
  simp only [Finset.singleton_union]
  tauto
end ArrivalAuxiliary

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

-- Source: Solutions.ConditionalHistorySupport
open MeasureTheory ProbabilityTheory RGMISFast
namespace ConditionalHistorySupport
open Classical ConditionalRankBand ExponentialMemoryless
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma shifted_ae_ge (θ : ℝ) : ∀ᵐx∂shifted θ, θ≤x := by
  rw [shifted,ae_map_iff (by fun_prop) (show MeasurableSet {x : ℝ|θ≤x} from measurableSet_Ici)]
  filter_upwards [exp_one_ae_nonnegative] with x hx
  linarith
lemma ae_support (r₀ : V→ℝ) (θ : ℝ) (hθ : 0≤θ) (hr₀ : IsHistory r₀ θ) :
    ∀ᵐr∂condLaw r₀ θ ∅ (fun _=>0), (∀v,0≤r v) ∧
      (∀v,r v<θ ↔ r₀ v<θ) ∧ (∀v,r₀ v<θ → r v=r₀ v) := by
  have hc (v : V) : ∀ᵐx∂marginal r₀ θ ∅ (fun _=>0) v,
      0≤x ∧ (x<θ ↔ r₀ v<θ) ∧ (r₀ v<θ → x=r₀ v) := by
    by_cases he : r₀ v<θ
    · simp only [marginal,if_pos he]
      exact (ae_dirac_iff (by measurability)).mpr ⟨hr₀.1 v,Iff.rfl,fun _=>rfl⟩
    · simp only [marginal,if_neg he,Finset.notMem_empty,↓reduceIte]
      filter_upwards [shifted_ae_ge θ] with x hx
      exact ⟨hθ.trans hx,iff_of_false (not_lt_of_ge hx) he,fun h=>(he h).elim⟩
  have hh (v : V) : ∀ᵐr∂Measure.pi (marginal r₀ θ ∅ (fun _=>0)),
      0≤r v ∧ (r v<θ ↔ r₀ v<θ) ∧ (r₀ v<θ → r v=r₀ v) :=
    Measure.tendsto_eval_ae_ae.eventually (hc v)
  filter_upwards [ae_all_iff.mpr hh] with r hr
  exact ⟨fun v=>(hr v).1,fun v=>(hr v).2.1,fun v=>(hr v).2.2⟩
lemma activity_history (G : SimpleGraph V) [DecidableRel G.Adj] (r₀ r : V→ℝ) (θ : ℝ)
    (hp : ∀v,r v<θ ↔ r₀ v<θ) (he : ∀v,r₀ v<θ → r v=r₀ v) (A : Finset V) :
    ActiveAt G r θ A ↔ ActiveAt G r₀ θ A := by
  exact forall_congr' (fun v=>forall_congr' (fun _=>
    PinnedActivity.activity_prefix_congr G r r₀ θ hp (fun v hv=>he v ((hp v).mp hv)) v))
lemma S_nonneg (r : V→ℝ) (A : Finset V) (a : ℝ) (ha : 0≤a) (hr : ∀v∈A,0≤r v) : 0≤S r A a := by
  unfold S rbar
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun v hv=>le_min (hr v hv) (Real.exp_pos 2).le)
end ConditionalHistorySupport

-- Source: Solutions.ConditionalCoordinatePinning
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace ConditionalCoordinatePinning
open Classical CoordinateDisintegration ConditionalRankBand
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma pin_map (r₀ rA : V→ℝ) (θ : ℝ) (A : Finset V) (hA : ∀v∈A,θ ≤ r₀ v) :
    (condLaw r₀ θ ∅ (fun _=>0)).map (fun q=>overlay A (rA,q)) = condLaw r₀ θ A rA := by
  haveI : IsProbabilityMeasure ((expMeasure 1).map (fun x : ℝ=>θ+x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hm (v : V) : Measurable (fun x : ℝ=>if v∈A then rA v else x) := by split_ifs <;> fun_prop
  change (Measure.pi (marginal r₀ θ ∅ (fun _=>0))).map (fun q v=>if v∈A then rA v else q v) = _
  rw [Measure.pi_map_pi (fun v=>(hm v).aemeasurable)]
  unfold condLaw
  congr 1
  funext v
  by_cases hv : v∈A
  · have he : ¬r₀ v<θ := not_lt_of_ge (hA v hv)
    simp [marginal,hv,he]
  · simp only [if_neg hv,Measure.map_id]
    simp [marginal,hv]
lemma charge_overlay (r q : V→ℝ) (A : Finset V) (a : ℝ) : S (overlay A (r,q)) A a = S r A a := by
  unfold S rbar
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [overlay,hv]
lemma overlay_mem (r q : V→ℝ) (A : Finset V) (v : V) (hv : v∈A) : overlay A (r,q) v = r v := by
  simp [overlay,hv]
end ConditionalCoordinatePinning

-- Source: Solutions.FiniteCoordinateIndependence
open MeasureTheory ProbabilityTheory
namespace FiniteCoordinateIndependence
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def fill (W : Finset V) (a : ℝ) (r : ↥(Wᶜ) → ℝ) : V → ℝ :=
  fun v => if h : v ∈ Wᶜ then r ⟨v,h⟩ else a
lemma fill_measurable (W : Finset V) (a : ℝ) : Measurable (fill W a) := by
  apply measurable_pi_lambda
  intro v
  unfold fill
  split_ifs <;> fun_prop
lemma independent_box (μ : V → Measure ℝ) [∀v, IsProbabilityMeasure (μ v)]
    (W : Finset V) (a : ℝ) (E : Set (V → ℝ)) (hE : MeasurableSet E)
    (B : V → Set ℝ) (hB : ∀v, MeasurableSet (B v)) :
    Measure.pi μ {r | fill W a (fun v : ↥(Wᶜ) => r v) ∈ E ∧ ∀v∈W,r v ∈ B v} =
      Measure.pi μ {r | fill W a (fun v : ↥(Wᶜ) => r v) ∈ E} * ∏v∈W, μ v (B v) := by
  have hi : iIndepFun (fun v (r : V → ℝ) => r v) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hh := hi.indepFun_finset (Wᶜ) W disjoint_compl_left (fun v => measurable_pi_apply v)
  have he := hh.measure_inter_preimage_eq_mul
    (fill W a ⁻¹' E) (Set.univ.pi (fun v : W => B v))
    (hE.preimage (fill_measurable W a)) (MeasurableSet.univ_pi (fun v => hB v))
  have hb : (fun r : V → ℝ => fun v : W => r v) ⁻¹' (Set.univ.pi (fun v : W => B v)) =
      (W : Set V).pi B := by
    ext r
    simp
  rw [hb,Measure.pi_pi_finset] at he
  convert he using 1 <;> congr 1
end FiniteCoordinateIndependence

-- Source: Solutions.FiniteCoordinateThinning
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FiniteCoordinateIndependence
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma thinning (μ : V → Measure ℝ) [∀v, IsProbabilityMeasure (μ v)]
    (W : Finset V) (a : ℝ) (E : Set (V → ℝ)) (hE : MeasurableSet E)
    (hlate : ∀r∈E, ∀v∈W, a ≤ r v)
    (hpin : ∀r, (∀v∈W,a ≤ r v) →
      (r∈E ↔ fill W a (fun v : ↥(Wᶜ) => r v) ∈ E))
    (B : Set ℝ) (hB : MeasurableSet B) (hBa : B ⊆ Set.Ici a)
    (q : ℝ≥0∞) (hq : ∀v∈W, μ v B = q * μ v (Set.Ici a)) :
    Measure.pi μ {r | r∈E ∧ ∀v∈W,r v∈B} = q^W.card * Measure.pi μ E := by
  have hbase : E = {r | fill W a (fun v : ↥(Wᶜ) => r v) ∈ E ∧ ∀v∈W,r v∈Set.Ici a} := by
    ext r
    constructor
    · intro hr
      exact ⟨(hpin r (hlate r hr)).mp hr,hlate r hr⟩
    · rintro ⟨hr,h⟩
      exact (hpin r h).mpr hr
  have hband : {r | r∈E ∧ ∀v∈W,r v∈B} =
      {r | fill W a (fun v : ↥(Wᶜ) => r v) ∈ E ∧ ∀v∈W,r v∈B} := by
    ext r
    constructor
    · rintro ⟨hr,h⟩
      exact ⟨(hpin r (hlate r hr)).mp hr,h⟩
    · rintro ⟨hr,h⟩
      exact ⟨(hpin r (fun v hv => hBa (h v hv))).mpr hr,h⟩
  rw [hband,independent_box μ W a E hE (fun _=>B) (fun _=>hB)]
  conv_rhs => rw [hbase,independent_box μ W a E hE (fun _=>Set.Ici a) (fun _=>measurableSet_Ici)]
  rw [Finset.prod_congr rfl hq,Finset.prod_mul_distrib,Finset.prod_const]
  ac_rfl
end FiniteCoordinateIndependence

-- Source: Theorems.Thm_RGMISFast_lemma_5_1
set_option autoImplicit false


/-!
# Attached sets and disjoint percolation certificates

An attached set is a set of nonroots each of whose vertices is reachable from
some root inside the induced vertex set. The percolation certificate retains
all of its nonroots and rejects its external boundary. Distinct attached sets
have incompatible certificates. This is the deterministic disjointness step
in the attached-set neighborhood inequality.
-/

namespace RGMISGeneral.Polynomial

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Graph steps whose destination lies in a specified finite vertex set. -/
def stepWithin (G : SimpleGraph V) (S : Finset V) (v w : V) : Prop :=
  G.Adj v w ∧ w ∈ S

/-- Every nonroot is joined to some root using only the chosen vertices. -/
def Attached (G : SimpleGraph V) (A T : Finset V) : Prop :=
  Disjoint A T ∧ ∀ v ∈ T, ∃ a ∈ A,
    Relation.ReflTransGen (stepWithin G (A ∪ T)) a v

/-- Vertices outside the chosen set with a neighbor inside it. -/
noncomputable def externalBoundary (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter fun w => w ∉ S ∧ ∃ v ∈ S, G.Adj v w

@[simp] theorem mem_externalBoundary {G : SimpleGraph V} {S : Finset V} {w : V} :
    w ∈ externalBoundary G S ↔ w ∉ S ∧ ∃ v ∈ S, G.Adj v w := by
  simp [externalBoundary]

/-- An outcome retains the nonroots and rejects the entire external boundary.
Roots are forced to be present separately, and need no coin toss. -/
def PercolationCertificate (G : SimpleGraph V) (A T : Finset V) (ω : V → Bool) : Prop :=
  (∀ v ∈ T, ω v = true) ∧ ∀ v ∈ externalBoundary G (A ∪ T), ω v = false

omit [Fintype V] in
theorem attached_empty (G : SimpleGraph V) (A : Finset V) : Attached G A ∅ := by
  simp [Attached]

theorem disjoint_externalBoundary (G : SimpleGraph V) (S : Finset V) :
    Disjoint S (externalBoundary G S) := by
  apply Finset.disjoint_left.mpr
  intro v hv hboundary
  exact (mem_externalBoundary.mp hboundary).1 hv

private theorem certificate_path_stays
    {G : SimpleGraph V} {A T U : Finset V} {ω : V → Bool}
    (hT : PercolationCertificate G A T ω)
    (hU : PercolationCertificate G A U ω)
    {a v : V} (ha : a ∈ A)
    (hpath : Relation.ReflTransGen (stepWithin G (A ∪ T)) a v) :
    v ∈ A ∪ U := by
  induction hpath with
  | refl => exact Finset.mem_union_left _ ha
  | @tail b c hpath hstep ih =>
      by_contra hc
      have hcb : c ∈ externalBoundary G (A ∪ U) :=
        mem_externalBoundary.mpr ⟨hc, b, ih, hstep.1⟩
      have hcT : c ∈ T := by
        rcases Finset.mem_union.mp hstep.2 with hca | hct
        · exact (hc (Finset.mem_union_left _ hca)).elim
        · exact hct
      have htrue := hT.1 c hcT
      have hfalse := hU.2 c hcb
      simp_all

/-- Two attached sets satisfying the same certificate must coincide. -/
theorem attached_certificate_unique
    {G : SimpleGraph V} {A T U : Finset V} {ω : V → Bool}
    (hT : Attached G A T) (hU : Attached G A U)
    (hcT : PercolationCertificate G A T ω)
    (hcU : PercolationCertificate G A U ω) : T = U := by
  have inclusion : ∀ {T U : Finset V}, Attached G A T →
      Attached G A U → PercolationCertificate G A T ω →
      PercolationCertificate G A U ω → T ⊆ U := by
    intro T U hT _ hcT hcU v hv
    obtain ⟨a, ha, hpath⟩ := hT.2 v hv
    have hin := certificate_path_stays hcT hcU ha hpath
    rcases Finset.mem_union.mp hin with hA | hU
    · exact (Finset.disjoint_left.mp hT.1 hA hv).elim
    · exact hU
  exact Finset.Subset.antisymm (inclusion hT hU hcT hcU)
    (inclusion hU hT hcU hcT)

/-- The events used in the percolation counting argument are pairwise disjoint. -/
theorem attached_certificate_disjoint
    {G : SimpleGraph V} {A T U : Finset V}
    (hT : Attached G A T) (hU : Attached G A U) (hne : T ≠ U) :
    Disjoint {ω | PercolationCertificate G A T ω}
      {ω | PercolationCertificate G A U ω} := by
  apply Set.disjoint_left.mpr
  intro ω hcT hcU
  exact hne (attached_certificate_unique hT hU hcT hcU)

end RGMISGeneral.Polynomial

/-!
# Finite Bernoulli encoding

All probabilities below are explicit finite sums of product weights. This
avoids any stochastic-process assumptions in the percolation counting step.
-/

namespace RGMISGeneral.Polynomial

open Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The mass of a finite independent Bernoulli outcome. -/
def bernoulliWeight (p : ℝ) (ω : V → Bool) : ℝ :=
  ∏ v, if ω v then p else 1 - p

omit [DecidableEq V] in
theorem bernoulliWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : V → Bool) : 0 ≤ bernoulliWeight p ω := by
  apply Finset.prod_nonneg
  intro v _
  split <;> linarith

theorem sum_bernoulliWeight (p : ℝ) :
    ∑ ω : V → Bool, bernoulliWeight p ω = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_sum (fun (_ : V) (b : Bool) => if b then p else 1 - p)]
  simp

/-- A cylinder specifies present and absent coordinates. -/
def Cylinder (Y B : Finset V) (ω : V → Bool) : Prop :=
  (∀ v ∈ Y, ω v = true) ∧ ∀ v ∈ B, ω v = false

private theorem cylinder_indicator_product (Y B : Finset V)
    (p : ℝ) (ω : V → Bool) :
    (if Cylinder Y B ω then bernoulliWeight p ω else 0) =
      ∏ v, if (v ∈ Y → ω v = true) ∧ (v ∈ B → ω v = false)
        then (if ω v then p else 1 - p) else 0 := by
  by_cases h : Cylinder Y B ω
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro v _
    simp only [if_pos (show (v ∈ Y → ω v = true) ∧ (v ∈ B → ω v = false) from ⟨h.1 v, h.2 v⟩)]
  · rw [if_neg h]
    symm
    have hex : ∃ v, ¬ ((v ∈ Y → ω v = true) ∧ (v ∈ B → ω v = false)) := by
      by_contra hnot
      apply h
      exact ⟨fun v hv => (not_not.mp (not_exists.mp hnot v)).1 hv,
        fun v hv => (not_not.mp (not_exists.mp hnot v)).2 hv⟩
    obtain ⟨v, hv⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)

/-- Exact cylinder probability in a finite independent Bernoulli space. -/
theorem cylinder_weight_sum (Y B : Finset V) (hdisj : Disjoint Y B) (p : ℝ) :
    ∑ ω : V → Bool, (if Cylinder Y B ω then bernoulliWeight p ω else 0) =
      p ^ Y.card * (1 - p) ^ B.card := by
  simp_rw [cylinder_indicator_product]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    if (v ∈ Y → b = true) ∧ (v ∈ B → b = false)
      then (if b then p else 1 - p) else 0)]
  have hcoord : ∀ v : V,
      (∑ b : Bool, if (v ∈ Y → b = true) ∧ (v ∈ B → b = false)
        then (if b then p else 1 - p) else 0) =
        (if v ∈ Y then p else 1) * (if v ∈ B then 1 - p else 1) := by
    intro v
    have hd : v ∈ Y → v ∈ B → False := fun hy hb =>
      Finset.disjoint_left.mp hdisj hy hb
    by_cases hy : v ∈ Y <;> by_cases hb : v ∈ B <;>
      simp_all
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_mem]

/-- Arbitrarily many incompatible cylinders have total weight at most one. -/
theorem sum_disjoint_cylinder_weights_le_one
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (Y B : ι → Finset V)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hdisj : ∀ i ∈ F, Disjoint (Y i) (B i))
    (hunique : ∀ ω, ∀ i ∈ F, ∀ j ∈ F,
      Cylinder (Y i) (B i) ω → Cylinder (Y j) (B j) ω → i = j) :
    ∑ i ∈ F, p ^ (Y i).card * (1 - p) ^ (B i).card ≤ 1 := by
  have hpoint (ω : V → Bool) :
      ∑ i ∈ F, (if Cylinder (Y i) (B i) ω then bernoulliWeight p ω else 0)
        ≤ bernoulliWeight p ω := by
    by_cases hex : ∃ i ∈ F, Cylinder (Y i) (B i) ω
    · obtain ⟨i, hi, hc⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [hc]
      · intro j hj hji
        rw [if_neg]
        intro hcj
        exact hji (hunique ω j hj i hi hcj hc)
      · exact fun hni => (hni hi).elim
    · have hz : ∀ i ∈ F, ¬ Cylinder (Y i) (B i) ω := by simpa using hex
      simp only [Finset.sum_congr rfl (fun i hi => if_neg (hz i hi)), Finset.sum_const_zero]
      exact bernoulliWeight_nonneg hp hp1 ω
  calc
    _ = ∑ i ∈ F, ∑ ω : V → Bool,
        (if Cylinder (Y i) (B i) ω then bernoulliWeight p ω else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (cylinder_weight_sum (Y i) (B i) (hdisj i hi) p).symm
    _ = ∑ ω : V → Bool, ∑ i ∈ F,
        (if Cylinder (Y i) (B i) ω then bernoulliWeight p ω else 0) := Finset.sum_comm
    _ ≤ ∑ ω : V → Bool, bernoulliWeight p ω :=
      Finset.sum_le_sum fun ω _ => hpoint ω
    _ = 1 := sum_bernoulliWeight p

/-- The exact percolation inequality for any family of attached sets. -/
theorem attached_percolation_bound (G : SimpleGraph V) (A : Finset V)
    (F : Finset (Finset V)) (hF : ∀ T ∈ F, Attached G A T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ T ∈ F, p ^ T.card * (1 - p) ^ (externalBoundary G (A ∪ T)).card ≤ 1 := by
  apply sum_disjoint_cylinder_weights_le_one F id
    (fun T => externalBoundary G (A ∪ T)) p hp hp1
  · intro T _
    exact Finset.disjoint_of_subset_left Finset.subset_union_right
      (disjoint_externalBoundary G (A ∪ T))
  · intro ω T hT U hU hcT hcU
    exact attached_certificate_unique (hF T hT) (hF U hU) hcT hcU

end RGMISGeneral.Polynomial

/-!
# The finite counting identity behind the survival drift

This file proves the combinatorial loss identity for one greedy deletion.
It does not assert that a rank process has a particular infinitesimal law;
that probability-theoretic step remains separate.
-/

namespace RGMISGeneral.Polynomial

open Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nonroot arrivals which destroy the specified root-and-attached vertex set. -/
noncomputable def killingArrivals (G : SimpleGraph V) (A T : Finset V) : Finset V :=
  Finset.univ.filter fun w => w ∉ A ∧
    (w ∈ T ∨ ∃ v ∈ A ∪ T, G.Adj v w)

@[simp] theorem mem_killingArrivals {G : SimpleGraph V} {A T : Finset V} {w : V} :
    w ∈ killingArrivals G A T ↔
      w ∉ A ∧ (w ∈ T ∨ ∃ v ∈ A ∪ T, G.Adj v w) := by
  simp [killingArrivals]

/-- The killing neighborhood consists of the chosen nonroots and its boundary. -/
theorem killingArrivals_eq_union {G : SimpleGraph V} {A T : Finset V}
    (hdisj : Disjoint A T) :
    killingArrivals G A T = T ∪ externalBoundary G (A ∪ T) := by
  ext w
  have hd : w ∈ T → w ∉ A := fun ht ha => Finset.disjoint_left.mp hdisj ha ht
  simp only [mem_killingArrivals, Finset.mem_union, mem_externalBoundary]
  by_cases hT : w ∈ T <;> simp_all

theorem killingArrivals_card {G : SimpleGraph V} {A T : Finset V}
    (hdisj : Disjoint A T) :
    (killingArrivals G A T).card = T.card + (externalBoundary G (A ∪ T)).card := by
  rw [killingArrivals_eq_union hdisj, Finset.card_union_of_disjoint]
  exact Finset.disjoint_of_subset_left Finset.subset_union_right
    (disjoint_externalBoundary G (A ∪ T))


end RGMISGeneral.Polynomial


/-!
# The analytic neighborhood inequality from a percolation estimate

The combinatorial percolation inequality is an explicit hypothesis. The
analytic implication below is independent of how that hypothesis is obtained.
-/

namespace RGMISGeneral.Polynomial

open scoped BigOperators

/-- A finite, equally weighted Jensen inequality for the exponential. -/
theorem card_mul_exp_average_le_sum_exp {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ) :
    (s.card : ℝ) * Real.exp ((∑ i ∈ s, f i) / s.card) ≤ ∑ i ∈ s, Real.exp (f i) := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  let μ : ℝ := (∑ i ∈ s, f i) / s.card
  have hpoint (i : ι) : Real.exp μ * (1 + (f i - μ)) ≤ Real.exp (f i) := by
    calc
      Real.exp μ * (1 + (f i - μ)) ≤ Real.exp μ * Real.exp (f i - μ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (f i - μ)]
      _ = Real.exp (f i) := by rw [← Real.exp_add]; congr 1; ring
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ s) ↦ hpoint i)
  have hidentity : (∑ i ∈ s, Real.exp μ * (1 + (f i - μ))) =
      (s.card : ℝ) * Real.exp μ := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    dsimp [μ]
    field_simp
    ring
  rw [hidentity] at hsum
  exact hsum

/-- Reparameterizing the Bernoulli probability avoids a boundary optimization:
`1 - exp (-x)` is always positive and dominates `x * exp (-x)`. -/
theorem exponential_probability_lower (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at h
  nlinarith

/-- The analytic form of the neighborhood inequality. It suffices to know
the mean degree is positive; individual lower degree bounds are not used.

The hypothesis is the whole family of Bernoulli percolation estimates. The
choice `p = 1 - exp (-k / d̄)` yields the exact factor `exp 1`, including the
case where the mean degree equals `k`. -/
theorem card_le_exp_mul_average_div_pow_of_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℝ) (k : ℕ)
    (hk : 0 < k)
    (hd : 0 < (∑ i ∈ s, d i) / (s.card : ℝ))
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - (k : ℝ))) ≤ 1) :
    (s.card : ℝ) ≤
      (Real.exp 1 * ((∑ i ∈ s, d i) / (s.card : ℝ)) / (k : ℝ)) ^ k := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hn : (s.card : ℝ) ≠ 0 := ne_of_gt hnpos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  let dbar : ℝ := (∑ i ∈ s, d i) / (s.card : ℝ)
  have hdbar : 0 < dbar := hd
  let x : ℝ := (k : ℝ) / dbar
  have hx : 0 < x := div_pos hkpos hdbar
  have hxd : x * dbar = (k : ℝ) := by
    dsimp [x]
    exact div_mul_cancel₀ _ hdbar.ne'
  let p : ℝ := 1 - Real.exp (-x)
  have hp : 0 < p := by
    dsimp [p]
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
    linarith
  have hpone : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-x)]
  have honep : 1 - p = Real.exp (-x) := by dsimp [p]; ring
  have hpower (i : ι) : (1 - p) ^ (d i - (k : ℝ)) =
      Real.exp (-x * (d i - (k : ℝ))) := by
    rw [honep, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hper := hpercolation p hp hpone
  simp_rw [hpower] at hper
  rw [← Finset.mul_sum] at hper
  have hjensen := card_mul_exp_average_le_sum_exp s hs
    (fun i ↦ -x * (d i - (k : ℝ)))
  have havg : (∑ i ∈ s, -x * (d i - (k : ℝ))) / (s.card : ℝ) =
      -x * (dbar - (k : ℝ)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [dbar]
    field_simp
  rw [havg] at hjensen
  have hweighted := mul_le_mul_of_nonneg_left hjensen (pow_nonneg hp.le k)
  have hJ : (s.card : ℝ) * p ^ k * Real.exp (-x * (dbar - (k : ℝ))) ≤ 1 := by
    nlinarith [hper, hweighted]
  have hlower : x * Real.exp (-x) ≤ p := exponential_probability_lower x
  have hlowpow : (x * Real.exp (-x)) ^ k ≤ p ^ k :=
    pow_le_pow_left₀ (by positivity) hlower k
  have hlowmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlowpow hnpos.le)
    (Real.exp_pos (-x * (dbar - (k : ℝ)))).le
  have hexpidentity :
      (x * Real.exp (-x)) ^ k * Real.exp (-x * (dbar - (k : ℝ))) =
        (x * Real.exp (-1)) ^ k := by
    calc
      _ = x ^ k * Real.exp ((k : ℝ) * (-x) + (-x * (dbar - (k : ℝ)))) := by
        rw [mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      _ = x ^ k * Real.exp (-(k : ℝ)) := by
        congr 2
        nlinarith [hxd]
      _ = (x * Real.exp (-1)) ^ k := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hlow : (s.card : ℝ) * (x * Real.exp (-1)) ^ k ≤ 1 := by
    calc
      _ = (s.card : ℝ) * (x * Real.exp (-x)) ^ k *
          Real.exp (-x * (dbar - (k : ℝ))) := by rw [mul_assoc, hexpidentity]
      _ ≤ (s.card : ℝ) * p ^ k * Real.exp (-x * (dbar - (k : ℝ))) := hlowmul
      _ ≤ 1 := hJ
  have hinverse : (x * Real.exp (-1)) ^ k * (Real.exp 1 * dbar / (k : ℝ)) ^ k = 1 := by
    rw [← mul_pow]
    have hbase : (x * Real.exp (-1)) * (Real.exp 1 * dbar / (k : ℝ)) = 1 := by
      rw [Real.exp_neg]
      dsimp [x]
      field_simp
    rw [hbase, one_pow]
  have hfinal := mul_le_mul_of_nonneg_right hlow
    (pow_nonneg (by positivity : 0 ≤ Real.exp 1 * dbar / (k : ℝ)) k)
  rw [mul_assoc, hinverse, mul_one, one_mul] at hfinal
  exact hfinal

/-- The corresponding lower bound on the total degree, in the form used
by a differential inequality for the expected number of attached sets. -/
theorem sum_ge_card_rpow_of_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℝ) (k : ℕ)
    (hk : 0 < k)
    (hd : 0 < (∑ i ∈ s, d i) / (s.card : ℝ))
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - (k : ℝ))) ≤ 1) :
    (k : ℝ) / Real.exp 1 * (s.card : ℝ) ^ (1 + (k : ℝ)⁻¹) ≤ ∑ i ∈ s, d i := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbound := card_le_exp_mul_average_div_pow_of_percolation s hs d k hk hd hpercolation
  have hbase : 0 ≤ Real.exp 1 * ((∑ i ∈ s, d i) / (s.card : ℝ)) / (k : ℝ) := by
    positivity
  have hroot := Real.rpow_le_rpow hnpos.le hbound (inv_nonneg.mpr hkpos.le)
  rw [Real.pow_rpow_inv_natCast hbase (Nat.ne_of_gt hk)] at hroot
  have hscaled := mul_le_mul_of_nonneg_left hroot
    (by positivity : 0 ≤ (k : ℝ) / Real.exp 1 * (s.card : ℝ))
  have hright : (k : ℝ) / Real.exp 1 * (s.card : ℝ) *
      (Real.exp 1 * ((∑ i ∈ s, d i) / (s.card : ℝ)) / (k : ℝ)) = ∑ i ∈ s, d i := by
    field_simp
  rw [hright] at hscaled
  rw [Real.rpow_add hnpos, Real.rpow_one]
  nlinarith [hscaled]

/-- Natural-degree version. The lower bound `k ≤ d i` both guarantees a
positive mean and identifies natural subtraction with real subtraction. -/
theorem card_le_exp_mul_average_div_pow_of_nat_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℕ) (k : ℕ)
    (hk : 0 < k) (hd : ∀ i ∈ s, k ≤ d i)
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - k)) ≤ 1) :
    (s.card : ℝ) ≤
      (Real.exp 1 * ((∑ i ∈ s, (d i : ℝ)) / (s.card : ℝ)) / (k : ℝ)) ^ k := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (s.card : ℝ) * (k : ℝ) ≤ ∑ i ∈ s, (d i : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (k : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ by exact_mod_cast hd i hi)
  have hmean : 0 < (∑ i ∈ s, (d i : ℝ)) / (s.card : ℝ) :=
    div_pos ((mul_pos hnpos hkpos).trans_le hsum) hnpos
  apply card_le_exp_mul_average_div_pow_of_percolation s hs (fun i ↦ (d i : ℝ)) k hk hmean
  intro p hp hpone
  convert hpercolation p hp hpone using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.cast_sub (hd i hi), Real.rpow_natCast]

/-- Total-degree version with natural degrees, ready to use with a finite
family of connected sets. -/
theorem sum_ge_card_rpow_of_nat_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℕ) (k : ℕ)
    (hk : 0 < k) (hd : ∀ i ∈ s, k ≤ d i)
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - k)) ≤ 1) :
    (k : ℝ) / Real.exp 1 * (s.card : ℝ) ^ (1 + (k : ℝ)⁻¹) ≤ ∑ i ∈ s, (d i : ℝ) := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (s.card : ℝ) * (k : ℝ) ≤ ∑ i ∈ s, (d i : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (k : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ by exact_mod_cast hd i hi)
  have hmean : 0 < (∑ i ∈ s, (d i : ℝ)) / (s.card : ℝ) :=
    div_pos ((mul_pos hnpos hkpos).trans_le hsum) hnpos
  apply sum_ge_card_rpow_of_percolation s hs (fun i ↦ (d i : ℝ)) k hk hmean
  intro p hp hpone
  convert hpercolation p hp hpone using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.cast_sub (hd i hi), Real.rpow_natCast]

end RGMISGeneral.Polynomial

/-!
# The attached-set neighborhood inequality

This is the unconditional combinatorial lemma from the manuscript, with
neighborhoods computed from the graph. The Bernoulli estimate is proved from
certificate disjointness rather than supplied as an assumption.
-/

namespace RGMISGeneral.Polynomial

open Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree sum lower bound for any family of distinct attached `k`-sets. -/
theorem attached_neighborhood_inequality
    (G : SimpleGraph V) (A : Finset V) (F : Finset (Finset V))
    (k : ℕ) (hk : 0 < k)
    (hF : ∀ T ∈ F, Attached G A T ∧ T.card = k) :
    (k : ℝ) / Real.exp 1 * (F.card : ℝ) ^ (1 + (k : ℝ)⁻¹) ≤
      ∑ T ∈ F, ((killingArrivals G A T).card : ℝ) := by
  by_cases hempty : F = ∅
  · subst F
    simp [Real.zero_rpow (by positivity : (1 + (k : ℝ)⁻¹) ≠ 0)]
  have hn : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  apply sum_ge_card_rpow_of_nat_percolation F hn
    (fun T => (killingArrivals G A T).card) k hk
  · intro T hT
    rw [killingArrivals_card (hF T hT).1.1, (hF T hT).2]
    omega
  · intro p hp hp1
    have hper := attached_percolation_bound G A F (fun T hT => (hF T hT).1)
      p hp.le hp1.le
    convert hper using 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [killingArrivals_card (hF T hT).1.1, (hF T hT).2]
    simp

end RGMISGeneral.Polynomial

open RGMISFast RGMISGeneral.Polynomial
lemma mission_attached_to_existing {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (A W : Finset V) (h : IsAttached H A W) : Attached H A W := by
  refine ⟨h.1,?_⟩
  intro w hw
  obtain ⟨u,hu,hr⟩ := h.2 w hw
  refine ⟨u,hu,?_⟩
  have hh := (SimpleGraph.reachable_iff_reflTransGen (G := restrictTo H (↑(A ∪ W))) u w).mp hr
  clear hw hr
  induction hh with
  | refl => exact .refl
  | tail hp hxy ih => exact ih.tail ⟨hxy.1,hxy.2.2⟩

lemma mission_degree_eq_existing {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (u : V) (W : Finset V) : dW H u W = (killingArrivals H {u} W).card := by
  classical
  simp [dW,killingArrivals]

theorem RGMISFast.lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V) (k : ℕ)
    (hk : 1 ≤ k) (S : Finset (Finset V)) (hS : S.Nonempty)
    (hSk : ∀ W ∈ S, W.card = k ∧ IsAttached H {u} W) :
    (k / Real.exp 1) * (S.card : ℝ) ^ (1 / (k : ℝ)) ≤
      (1 / (S.card : ℝ)) * ∑ W ∈ S, (dW H u W : ℝ) := by
  have hspos : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hb := attached_neighborhood_inequality H {u} S k hk
    (fun W hW => ⟨mission_attached_to_existing H {u} W (hSk W hW).2,(hSk W hW).1⟩)
  simp_rw [←mission_degree_eq_existing H u] at hb
  rw [Real.rpow_add hspos,Real.rpow_one] at hb
  have hh : (k / Real.exp 1) * (S.card : ℝ) ^ (1 / (k : ℝ)) ≤
      (∑ W ∈ S, (dW H u W : ℝ)) / (S.card : ℝ) := by
    apply (le_div_iff₀ hspos).mpr
    simp only [one_div]
    nlinarith [hb]
  simpa only [one_div,div_eq_inv_mul,mul_one] using hh



-- Source: Solutions.ArrivalLoss
open RGMISFast
open scoped BigOperators
namespace ArrivalLoss
open Classical
section
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] in
/-- The number lost under one arrival is the number of sets it kills. -/
theorem count_loss_eq_killed {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (kill : ι → Finset V) (w : V) :
    (F.card : ℝ) - ((F.filter fun i => w ∉ kill i).card : ℝ) =
      ((F.filter fun i => w ∈ kill i).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun i => w ∈ kill i)
  have hr : ((F.filter fun i => w ∈ kill i).card : ℝ) +
      ((F.filter fun i => w ∉ kill i).card : ℝ) = (F.card : ℝ) := by
    exact_mod_cast h
  linarith

omit [Fintype V] in
/-- Exact double counting of the total loss over all possible arrivals. -/
theorem sum_count_loss_eq_sum_killing_card {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (R : Finset V) (kill : ι → Finset V)
    (hkill : ∀ i ∈ F, kill i ⊆ R) :
    ∑ w ∈ R, ((F.card : ℝ) - ((F.filter fun i => w ∉ kill i).card : ℝ)) =
      ∑ i ∈ F, ((kill i).card : ℝ) := by
  simp_rw [count_loss_eq_killed]
  have hind (w : V) : ((F.filter fun i => w ∈ kill i).card : ℝ) =
      ∑ i ∈ F, if w ∈ kill i then (1 : ℝ) else 0 := by simp
  simp_rw [hind]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.inter_eq_right.mpr (hkill i hi)]

noncomputable def killers (H : SimpleGraph V) (u : V) (W : Finset V) : Finset V :=
  Finset.univ.filter (fun x => x ≠ u ∧ (x ∈ W ∨ ∃ y ∈ insert u W, H.Adj y x))

lemma killers_card (H : SimpleGraph V) (u : V) (W : Finset V) :
    (killers H u W).card = dW H u W := rfl

end

/-- Exact finite loss identity for the mission's active graph and counted family. -/
theorem dsSum_eq_total_loss {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    (dsSum G u k s r : ℝ) =
      ∑ x ∈ (Finset.univ.filter (fun x => x ≠ u ∧ s ≤ tau G r x)),
        ((countedW G u k s r).card -
          (((countedW G u k s r).filter
            (fun W => x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W)).card : ℝ)) := by
  let F := countedW G u k s r
  let R := Finset.univ.filter (fun x => x ≠ u ∧ s ≤ tau G r x)
  let kill := killers (restrictTo G {v | s ≤ tau G r v}) u
  have hkill : ∀ W ∈ F, kill W ⊆ R := by
    intro W hW x hx
    obtain ⟨hne, hxW | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hx).2
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hne, ?_⟩
      have hact := (Finset.mem_filter.mp hW).2.2.2.2
      exact hact x (Finset.mem_insert_of_mem hxW)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,hyx.2.2⟩
  have h := sum_count_loss_eq_sum_killing_card F R kill hkill
  rw [h]
  simp only [dsSum, Nat.cast_sum, killers_card, F, kill]
end ArrivalLoss

-- Source: Solutions.ExtensionCounts
open RGMISFast
namespace ExtensionCounts
open Classical RGMISGeneral.Polynomial
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V]
noncomputable def family (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (t : ℝ) (r : V → ℝ) : Finset (Finset V) :=
  Finset.univ.filter (fun W => W.card = k ∧ IsAttached G A W ∧ ActiveAt G r t (A ∪ W))
noncomputable def loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (t : ℝ) (r : V → ℝ) : ℕ :=
  ∑ W ∈ family G A k t r, (killingArrivals (restrictTo G {v | t ≤ tau G r v}) A W).card
lemma count_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (t : ℝ) (r : V → ℝ) : Ncount G A k t r = (family G A k t r).card := rfl
lemma family_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (s t : ℝ) (r q : V → ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) : family G A k s r = family G A k t q := by
  unfold family
  apply Finset.filter_congr
  intro W hW
  have ha : ActiveAt G r s (A ∪ W) ↔ ActiveAt G q t (A ∪ W) := by
    unfold ActiveAt
    simp_rw [h]
  rw [ha]
lemma loss_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (s t : ℝ) (r q : V → ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) : loss G A k s r = loss G A k t q := by
  have hf := family_congr G A k s t r q h
  have he : {v | s ≤ tau G r v} = {v | t ≤ tau G q v} := Set.ext h
  unfold loss
  rw [hf,he]
lemma killing_active (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (t : ℝ) (r : V → ℝ)
    (W : Finset V) (hW : W ∈ family G A k t r) (x : V)
    (hx : x ∈ killingArrivals (restrictTo G {v | t ≤ tau G r v}) A W) :
    x ∉ A ∧ t ≤ tau G r x := by
  obtain ⟨hn,hxW | ⟨y,hy,hyx⟩⟩ := mem_killingArrivals.mp hx
  · exact ⟨hn,(Finset.mem_filter.mp hW).2.2.2 x (Finset.mem_union_right _ hxW)⟩
  · exact ⟨hn,hyx.2.2⟩
lemma family_single_arrival (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (r : V → ℝ) (s t : ℝ) (hst : s ≤ t) (x : V) (hxA : x ∉ A)
    (hx : s ≤ r x ∧ r x < t) (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    family G A k t r = (family G A k s r).filter
      (fun W => x ∉ killingArrivals (restrictTo G {v | s ≤ tau G r v}) A W) := by
  ext W
  simp only [family,Finset.mem_filter,Finset.mem_univ,true_and]
  have ha : ActiveAt G r t (A ∪ W) ↔ ActiveAt G r s (A ∪ W) ∧
      x ∉ killingArrivals (restrictTo G {v | s ≤ tau G r v}) A W := by
    rw [SingleArrival.active_set_transition G r s t hst x (A ∪ W) hx hone]
    constructor
    · rintro ⟨hact,hkeep⟩
      refine ⟨hact,?_⟩
      intro hk
      obtain ⟨_,hw | ⟨y,hy,hyx⟩⟩ := mem_killingArrivals.mp hk
      · exact (hkeep (hact x (Finset.mem_union_right _ hw)) x (Finset.mem_union_right _ hw)).1 rfl
      · exact (hkeep hyx.2.2 y hy).2 hyx.1
    · rintro ⟨hact,hkeep⟩
      refine ⟨hact,?_⟩
      intro hxa v hv
      constructor
      · intro hvx
        subst v
        have hw : x ∈ W := (Finset.mem_union.mp hv).resolve_left hxA
        exact hkeep (mem_killingArrivals.mpr ⟨hxA,Or.inl hw⟩)
      · intro hadj
        exact hkeep (mem_killingArrivals.mpr ⟨hxA,Or.inr ⟨v,hv,hadj,hact v hv,hxa⟩⟩)
  rw [ha]
  tauto

lemma attached_active (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (s : ℝ) (r : V → ℝ) (W : Finset V)
    (hW : W ∈ family G A k s r) :
    IsAttached (restrictTo G {x | s ≤ tau G r x}) A W := by
  obtain ⟨_,hcard,hatt,hact⟩ := Finset.mem_filter.mp hW
  refine ⟨hatt.1,?_⟩
  have he : restrictTo (restrictTo G {x | s ≤ tau G r x}) (↑(A ∪ W)) = restrictTo G (↑(A ∪ W)) := by
    ext x y
    change ((G.Adj x y ∧ s ≤ tau G r x ∧ s ≤ tau G r y) ∧ x ∈ A ∪ W ∧ y ∈ A ∪ W) ↔
      (G.Adj x y ∧ x ∈ A ∪ W ∧ y ∈ A ∪ W)
    constructor
    · rintro ⟨⟨ha,_,_⟩,hx,hy⟩; exact ⟨ha,hx,hy⟩
    · rintro ⟨ha,hx,hy⟩; exact ⟨⟨ha,hact x hx,hact y hy⟩,hx,hy⟩
  intro w hw
  obtain ⟨v,hv,hpath⟩ := hatt.2 w hw
  exact ⟨v,hv,by rw [he]; exact hpath⟩
lemma loss_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (r : V → ℝ) :
    (k : ℝ) / Real.exp 1 * (Ncount G A k s r : ℝ) ^ (1+(k:ℝ)⁻¹) ≤
      (loss G A k s r : ℝ) := by
  have hh := attached_neighborhood_inequality (restrictTo G {x | s ≤ tau G r x}) A
    (family G A k s r) k hk (fun W hW =>
      ⟨mission_attached_to_existing _ A W (attached_active G A k s r W hW),
       (Finset.mem_filter.mp hW).2.1⟩)
  simpa only [loss,Nat.cast_sum,count_eq_card] using hh
end ExtensionCounts

-- Source: Solutions.ExtensionThinning
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace ExtensionThinning
open Classical ExtensionCounts ConditionalRankBand FiniteCoordinateIndependence
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma active_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (S : Finset V) :
    MeasurableSet {r : V → ℝ | ActiveAt G r a S} := by
  simp only [ActiveAt,Set.setOf_forall]
  exact MeasurableSet.iInter (fun v => MeasurableSet.iInter (fun _ => active_vertex_measurable G a v))
lemma candidate_measurable (G : SimpleGraph V) [DecidableRel G.Adj]
    (A W : Finset V) (k : ℕ) (a : ℝ) :
    MeasurableSet {r : V → ℝ | W∈family G A k a r} := by
  simp only [family,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (active_measurable G a (A∪W)))
lemma candidate_thinning (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ a : ℝ) (hθa : θ<a) (A W : Finset V) (rA : V → ℝ)
    (k : ℕ) (b : WithTop ℝ) (hab : (a:WithTop ℝ)<b) :
    condLaw r₀ θ A rA {r | W∈family G A k a r ∧ ∀v∈W,(r v:WithTop ℝ)<b} =
      ENNReal.ofReal (oneMinusExp a b)^W.card * condLaw r₀ θ A rA {r | W∈family G A k a r} := by
  by_cases hatt : IsAttached G A W
  · have hlate : ∀r∈{r | W∈family G A k a r}, ∀v∈W,a≤r v := by
      intro r hr v hv
      exact ArrivalAuxiliary.active_le_rank G r a v ((Finset.mem_filter.mp hr).2.2.2 v (Finset.mem_union_right A hv))
    have hpin : ∀r, (∀v∈W,a≤r v) →
        (W∈family G A k a r ↔ W∈family G A k a (fill W a (fun v : ↥(Wᶜ) => r v))) := by
      intro r hr
      have he : fill W a (fun v : ↥(Wᶜ) => r v) = (fun v=>if v∈W then a else r v) := by
        funext v
        by_cases hv : v∈W <;> simp [fill,hv]
      rw [he]
      rw [family_congr G A k a a r (fun v=>if v∈W then a else r v)
        (PinnedActivity.pinning_above_threshold G r (fun _=>a) a W hr (fun _ _=>le_rfl))]
    have hh := thinning (marginal r₀ θ A rA) W a _ (candidate_measurable G A W k a)
      hlate hpin (band a b) (band_measurable a b) (fun _ h=>h.1)
      (ENNReal.ofReal (oneMinusExp a b)) (fun v hv=>marginal_band r₀ θ a hθa A rA v
        (fun ha=>Finset.disjoint_left.mp hatt.1 ha hv) b hab)
    change (Measure.pi (marginal r₀ θ A rA)) _ = _ * (Measure.pi (marginal r₀ θ A rA)) _
    rw [← hh]
    congr 1
    ext r
    constructor
    · rintro ⟨hr,hb⟩
      exact ⟨hr,fun v hv=>⟨hlate r hr v hv,hb v hv⟩⟩
    · rintro ⟨hr,hb⟩
      exact ⟨hr,fun v hv=>(hb v hv).2⟩
  · simp [family,hatt]
noncomputable def retained (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (a : ℝ) (b : WithTop ℝ) (r : V → ℝ) : Finset (Finset V) :=
  (family G A k a r).filter (fun W=>∀v∈W,(r v:WithTop ℝ)<b)


lemma cutoff_measurable (W : Finset V) (b : WithTop ℝ) :
    MeasurableSet {r : V → ℝ | ∀v∈W,(r v:WithTop ℝ)<b} := by
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    simp only [WithTop.coe_lt_coe,Set.setOf_forall]
    exact MeasurableSet.iInter (fun v=>MeasurableSet.iInter (fun _=>
      measurableSet_lt (measurable_pi_apply v) measurable_const))
lemma retained_mem_measurable (G : SimpleGraph V) [DecidableRel G.Adj]
    (A W : Finset V) (k : ℕ) (a : ℝ) (b : WithTop ℝ) :
    MeasurableSet {r : V → ℝ | W∈retained G A k a b r} := by
  simp only [retained,Finset.mem_filter]
  exact (candidate_measurable G A W k a).inter (cutoff_measurable W b)
lemma integral_card {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    (F : Ω → Finset X) (μ : Measure Ω) (hm : ∀x,MeasurableSet {r|x∈F r}) :
    (∫⁻ r, ((F r).card:ℝ≥0∞) ∂μ) = ∑x, μ {r|x∈F r} := by
  have he (r : Ω) : ((F r).card:ℝ≥0∞) = ∑x, ({r|x∈F r}.indicator (fun _=> (1:ℝ≥0∞))) r := by
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
    simp
  simp_rw [he]
  rw [lintegral_finset_sum _ (fun x _=>(measurable_const.indicator (hm x)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_indicator (hm x)]
  simp
lemma integral_retained (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ a : ℝ) (hθa : θ<a) (A : Finset V) (rA : V → ℝ)
    (k : ℕ) (b : WithTop ℝ) (hab : (a:WithTop ℝ)<b) :
    (∫⁻ r, ((retained G A k a b r).card:ℝ≥0∞) ∂condLaw r₀ θ A rA) =
      ENNReal.ofReal (oneMinusExp a b)^k *
        (∫⁻ r, (Ncount G A k a r:ℝ≥0∞) ∂condLaw r₀ θ A rA) := by
  rw [integral_card _ _ (fun W=>retained_mem_measurable G A W k a b)]
  simp only [count_eq_card]
  rw [integral_card _ _ (fun W=>candidate_measurable G A W k a),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  simp only [retained,Finset.mem_filter]
  rw [candidate_thinning G r₀ θ a hθa A W rA k b hab]
  by_cases hc : W.card=k
  · rw [hc]
  · simp [family,hc]
lemma card_measurable {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    (F : Ω → Finset X) (hm : ∀x,MeasurableSet {r|x∈F r}) : Measurable (fun r=>(F r).card) := by
  have he (r : Ω) : (F r).card = ∑x, if x∈F r then 1 else 0 := by simp
  simp_rw [he]
  exact Finset.measurable_sum _ (fun x _=>Measurable.ite (hm x) measurable_const measurable_const)
lemma boundary_measurable (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (a : ℝ) (b : WithTop ℝ) : Measurable (fun r : V → ℝ=>KAB G r a b A) := by
  unfold KAB
  apply Measurable.ite (active_measurable G a A) _ measurable_const
  apply card_measurable
  intro v
  simp only [Finset.mem_filter]
  have hb : MeasurableSet {r : V → ℝ | (r v:WithTop ℝ)<b} := by
    simpa only [Finset.mem_singleton,forall_eq] using cutoff_measurable ({v}:Finset V) b
  exact (MeasurableSet.const _).inter ((active_vertex_measurable G a v).inter hb)
end ExtensionThinning

-- Source: Solutions.BadEventMeasurability
open MeasureTheory ProbabilityTheory RGMISFast
namespace BadEventMeasurability
open Classical
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma charge_measurable (A : Finset V) (a : ℝ) : Measurable (fun r : V→ℝ=>S r A a) := by
  unfold S rbar
  fun_prop
lemma gamma_measurable (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (a : ℝ) (b : WithTop ℝ) : Measurable (fun r : V→ℝ=>(GammaAB G r a b A).card) := by
  let code : (V→ℝ)→(V→Prop)×(V→Prop) := fun r=>(fun v=>a ≤ tau G r v,fun v=>(r v:WithTop ℝ)<b)
  have hc : Measurable code := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun v=>measurableSet_setOf.mp (active_vertex_measurable G a v))
    · apply measurable_pi_lambda
      intro v
      apply measurableSet_setOf.mp
      simpa only [Finset.mem_singleton,forall_eq] using ExtensionThinning.cutoff_measurable ({v}:Finset V) b
  have hf : (fun r : V→ℝ=>(GammaAB G r a b A).card).FactorsThrough code := by
    intro r q he
    have ha (v : V) : (a ≤ tau G r v) ↔ (a ≤ tau G q v) :=
      iff_of_eq (congrFun (congrArg Prod.fst he) v)
    have hb (v : V) : ((r v:WithTop ℝ)<b) ↔ ((q v:WithTop ℝ)<b) :=
      iff_of_eq (congrFun (congrArg Prod.snd he) v)
    have hA := activeAt_congr G a r q ha A
    have hgraph : restrictTo G {y|y∈A ∨ (a ≤ tau G r y ∧ (r y:WithTop ℝ)<b)} =
        restrictTo G {y|y∈A ∨ (a ≤ tau G q y ∧ (q y:WithTop ℝ)<b)} := by
      ext x y
      simp only [restrictTo,ha,hb,Set.mem_setOf_eq]
    simp only [GammaAB,hA,hgraph]
  obtain ⟨f,he⟩ := Function.factorsThrough_iff _ |>.mp hf
  rw [he]
  exact (measurable_of_countable f).comp hc
lemma bad_measurable (A : Finset V) (a L d : ℝ) (N : (V→ℝ)→ℕ) (hN : Measurable N) :
    MeasurableSet {r|d*(2*S r A a+L)<(N r:ℝ)} := by
  apply measurableSet_lt
  · exact measurable_const.mul ((measurable_const.mul (charge_measurable A a)).add_const L)
  · exact (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp hN
end BadEventMeasurability

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

-- Source: Solutions.ConditionalWeightedTail
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace ConditionalWeightedTail
open Classical ConditionalRankBand CoordinateDisintegration ConditionalCoordinatePinning
open ConditionalHistorySupport BadEventMeasurability RankChargeLaplace
variable {V : Type*} [Fintype V] [LinearOrder V]
set_option maxHeartbeats 1000000
lemma weighted_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V→ℝ) (θ a L d : ℝ) (hθ : 0 ≤ θ) (hθa : θ<a) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (N : (V→ℝ)→ℕ) (hN : Measurable N)
    (hactive : ∀r,0<N r → ActiveAt G r a A)
    (hbound : ActiveAt G r₀ θ A → ∀rA, (∀v∈A,a ≤ rA v) →
      condLaw r₀ θ A rA {r | d*(2*S rA A a+L)<(N r:ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(2*S rA A a+L)))) :
    condLaw r₀ θ ∅ (fun _=>0) {r | d*(2*S r A a+L)<(N r:ℝ)} ≤
      (if ActiveAt G r₀ θ A then 1 else 0) *
        (∫⁻r in {r|∀v∈A,a ≤ r v},ENNReal.ofReal (Real.exp (-(2*S r A a+L))) ∂condLaw r₀ θ ∅ (fun _=>0)) := by
  let μ := condLaw r₀ θ ∅ (fun _=>0)
  let E := {r : V→ℝ|d*(2*S r A a+L)<(N r:ℝ)}
  have hE : MeasurableSet E := bad_measurable A a L d N hN
  have hs (r : V→ℝ) (hr : ∀v∈A,0 ≤ r v) : 0 ≤ d*(2*S r A a+L) :=
    mul_nonneg hd (by have hh:=S_nonneg r A a (hθ.trans hθa.le) hr; linarith)
  have hpos (r : V→ℝ) (hr : ∀v∈A,0 ≤ r v) (he : r∈E) : 0<N r := by
    have hh : (0:ℝ)<N r := lt_of_le_of_lt (hs r hr) he
    exact_mod_cast hh
  by_cases hA : ActiveAt G r₀ θ A
  · rw [if_pos hA,one_mul]
    have hlate (v : V) (hv : v∈A) : θ ≤ r₀ v := ArrivalAuxiliary.active_le_rank G r₀ θ v (hA v hv)
    have heq : μ E = ∫⁻r,∫⁻q,E.indicator (fun _=>(1:ℝ≥0∞)) (overlay A (r,q)) ∂μ ∂μ := by
      rw [← lintegral_indicator_one hE]
      exact integral_overlay (marginal r₀ θ ∅ (fun _=>0)) A _ (measurable_const.indicator hE)
    change μ E ≤ _
    rw [heq,← lintegral_indicator (high_measurable A a)]
    apply lintegral_mono_ae
    filter_upwards [ae_support r₀ θ hθ hr₀] with r hr
    by_cases hra : ∀v∈A,a ≤ r v
    · rw [Set.indicator_of_mem (show r∈{z : V→ℝ|∀v∈A,a ≤ z v} from hra)]
      have hm : MeasurableSet {z : V→ℝ|d*(2*S r A a+L)<(N z:ℝ)} :=
        measurableSet_lt measurable_const ((measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp hN)
      have heinner : (∫⁻q,E.indicator (fun _=>(1:ℝ≥0∞)) (overlay A (r,q)) ∂μ) =
          condLaw r₀ θ A r {z|d*(2*S r A a+L)<(N z:ℝ)} := by
        rw [← pin_map r₀ r θ A hlate,← lintegral_indicator_one hm]
        have hmi : Measurable ({z : V→ℝ|d*(2*S r A a+L)<(N z:ℝ)}.indicator (1 : (V→ℝ)→ℝ≥0∞)) :=
          measurable_const.indicator hm
        have hpinMeas : Measurable (fun q : V→ℝ=>overlay A (r,q)) :=
          (overlay_measurable A).comp (measurable_const.prodMk measurable_id)
        rw [lintegral_map hmi hpinMeas]
        apply lintegral_congr
        intro q
        simp only [E,Set.indicator_apply,Set.mem_setOf_eq,charge_overlay,Pi.one_apply]
      rw [heinner]
      exact hbound hA r hra
    · rw [Set.indicator_of_notMem (show r∉{z : V→ℝ|∀v∈A,a ≤ z v} from hra)]
      apply le_of_eq
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with q
      apply Set.indicator_of_notMem
      intro he
      have hact := hactive _ (hpos _ (fun v hv=>by rw [overlay_mem r q A v hv]; exact hr.1 v) he)
      apply hra
      intro v hv
      have hh := ArrivalAuxiliary.active_le_rank G (overlay A (r,q)) a v (hact v hv)
      simpa only [overlay_mem r q A v hv] using hh
  · rw [if_neg hA,zero_mul]
    apply le_of_eq
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_support r₀ θ hθ hr₀] with r hr
    intro he
    have hact := hactive r (hpos r (fun v _=>hr.1 v) he)
    have hat : ActiveAt G r θ A := fun v hv=>hθa.le.trans (hact v hv)
    exact hA ((activity_history G r₀ r θ hr.2.1 hr.2.2 A).mp hat)
end ConditionalWeightedTail

-- Source: Solutions.AttachedSubsets

/-!
# Extracting an attached set of any smaller size

This is the deterministic exploration step converting a large retained
component union into a certificate with exactly `k` nonroot vertices.
-/

namespace RGMISGeneral.Polynomial

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem path_exits_set {R : V → V → Prop} {S : Finset V} {a v : V}
    (hpath : Relation.ReflTransGen R a v) (ha : a ∈ S) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y, y ∉ S ∧ R x y := by
  by_contra h
  have hclosed : ∀ x ∈ S, ∀ y, R x y → y ∈ S := by
    intro x hx y hxy
    by_contra hy
    exact h ⟨x, hx, y, hy, hxy⟩
  have hin : ∀ {x}, Relation.ReflTransGen R a x → x ∈ S := by
    intro x hx
    induction hx with
    | refl => exact ha
    | tail _ hxy ih => exact hclosed _ ih _ hxy
  exact hv (hin hpath)

/-- One may grow any proper attached subset by one vertex inside the larger set. -/
theorem attached_can_grow {G : SimpleGraph V} {A T U : Finset V}
    (hT : Attached G A T) (hU : Attached G A U)
    (_hsub : T ⊆ U) (hcard : T.card < U.card) :
    ∃ w ∈ U, w ∉ T ∧ Attached G A (insert w T) := by
  obtain ⟨v, hvU, hvT⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨a, ha, hpath⟩ := hU.2 v hvU
  have hvA : v ∉ A := fun hvA => Finset.disjoint_left.mp hU.1 hvA hvU
  have hvout : v ∉ A ∪ T := by simp [hvA, hvT]
  obtain ⟨x, hx, w, hwout, hxw⟩ :=
    path_exits_set hpath (Finset.mem_union_left T ha) hvout
  have hwA : w ∉ A := fun h => hwout (Finset.mem_union_left T h)
  have hwT : w ∉ T := fun h => hwout (Finset.mem_union_right A h)
  have hwU : w ∈ U := (Finset.mem_union.mp hxw.2).resolve_left hwA
  refine ⟨w, hwU, hwT, ?_, ?_⟩
  · exact Finset.disjoint_insert_right.mpr ⟨hwA, hT.1⟩
  · intro z hz
    have hmono : ∀ {v y}, stepWithin G (A ∪ T) v y →
        stepWithin G (A ∪ insert w T) v y := by
      intro v y h
      exact ⟨h.1, Finset.mem_union.mpr ((Finset.mem_union.mp h.2).imp id
        (fun hy => Finset.mem_insert_of_mem hy))⟩
    have hxPath : ∃ a ∈ A,
        Relation.ReflTransGen (stepWithin G (A ∪ T)) a x := by
      rcases Finset.mem_union.mp hx with hxA | hxT
      · exact ⟨x, hxA, .refl⟩
      · exact hT.2 x hxT
    rcases Finset.mem_insert.mp hz with hzw | hzT
    · subst z
      obtain ⟨b, hb, hbx⟩ := hxPath
      exact ⟨b, hb, (Relation.ReflTransGen.mono @hmono _ _ hbx).tail
        ⟨hxw.1, Finset.mem_union_right A (Finset.mem_insert_self w T)⟩⟩
    · obtain ⟨b, hb, hbz⟩ := hT.2 z hzT
      exact ⟨b, hb, Relation.ReflTransGen.mono @hmono _ _ hbz⟩

/-- A retained component union with at least `k` nonroots contains an attached
certificate of exactly `k` nonroots. -/
theorem exists_attached_subset_card {G : SimpleGraph V} {A U : Finset V}
    (hU : Attached G A U) (k : ℕ) (hk : k ≤ U.card) :
    ∃ T ⊆ U, Attached G A T ∧ T.card = k := by
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset _, attached_empty G A, by simp⟩
  | succ k ih =>
      obtain ⟨T, hTU, hT, hTk⟩ := ih (by omega)
      obtain ⟨w, hwU, hwT, hTw⟩ := attached_can_grow hT hU hTU (by omega)
      refine ⟨insert w T, Finset.insert_subset hwU hTU, hTw, ?_⟩
      simp [Finset.card_insert_of_notMem hwT, hTk]

end RGMISGeneral.Polynomial

-- Source: Solutions.ExtensionCertificates
open RGMISFast
namespace ExtensionCertificates
open Classical RGMISGeneral.Polynomial ExtensionCounts ExtensionThinning
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma attached_to_mission (G : SimpleGraph V) (A W : Finset V) (h : Attached G A W) :
    IsAttached G A W := by
  refine ⟨h.1,?_⟩
  intro w hw
  obtain ⟨x,hx,hp⟩ := h.2 w hw
  refine ⟨x,hx,?_⟩
  apply (SimpleGraph.reachable_iff_reflTransGen _ _).mpr
  have hh : ∀ {z}, Relation.ReflTransGen (stepWithin G (A∪W)) x z →
      z∈A∪W ∧ Relation.ReflTransGen (restrictTo G (↑(A∪W))).Adj x z := by
    intro z hz
    induction hz with
    | refl => exact ⟨Finset.mem_union_left W hx,.refl⟩
    | tail hp hxy ih => exact ⟨hxy.2,ih.2.tail ⟨hxy.1,ih.1,hxy.2⟩⟩
  exact (hh hp).2
lemma gamma_active (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (a : ℝ) (b : WithTop ℝ) (A : Finset V)
    (hA : ActiveAt G r a A) {w : V} (hw : w∈GammaAB G r a b A) :
    w∉A ∧ a≤tau G r w ∧ (r w:WithTop ℝ)<b := by
  rw [GammaAB,if_pos hA] at hw
  obtain ⟨_,hwn, x,hx,hp⟩ := Finset.mem_filter.mp hw
  refine ⟨hwn,?_⟩
  have hh := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hp
  have hm : ∀{z}, Relation.ReflTransGen
      (restrictTo G {y|y∈A ∨ (a≤tau G r y ∧ (r y:WithTop ℝ)<b)}).Adj x z →
      z∈A ∨ (a≤tau G r z ∧ (r z:WithTop ℝ)<b) := by
    intro z hz
    cases hz with
    | refl => exact Or.inl hx
    | tail _ hxy => exact hxy.2.2
  exact (hm hh).resolve_left hwn
lemma gamma_attached (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (a : ℝ) (b : WithTop ℝ) (A : Finset V)
    (hA : ActiveAt G r a A) : Attached G A (GammaAB G r a b A) := by
  refine ⟨Finset.disjoint_left.mpr (fun v hvA hv=> (gamma_active G r a b A hA hv).1 hvA),?_⟩
  intro w hw
  have hw' := hw
  rw [GammaAB,if_pos hA] at hw'
  obtain ⟨_,hwn,x,hx,hp⟩ := Finset.mem_filter.mp hw'
  refine ⟨x,hx,?_⟩
  let H := restrictTo G {y|y∈A ∨ (a≤tau G r y ∧ (r y:WithTop ℝ)<b)}
  have hm (z : V) (hz : Relation.ReflTransGen H.Adj x z) : z∈A∪GammaAB G r a b A := by
    by_cases hzA : z∈A
    · exact Finset.mem_union_left _ hzA
    · apply Finset.mem_union_right
      rw [GammaAB,if_pos hA]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzA,x,hx,(SimpleGraph.reachable_iff_reflTransGen _ _).mpr hz⟩
  have hh : Relation.ReflTransGen H.Adj x w := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hp
  have hc : ∀{z}, Relation.ReflTransGen H.Adj x z →
      Relation.ReflTransGen (stepWithin G (A∪GammaAB G r a b A)) x z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | tail hp hxy ih => exact ih.tail ⟨hxy.1,hm _ (hp.tail hxy)⟩
  exact hc hh
lemma gamma_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (a : ℝ) (b : WithTop ℝ) (A : Finset V) (k : ℕ)
    (hk : 1≤k) (hcard : k≤(GammaAB G r a b A).card) :
    (retained G A k a b r).Nonempty := by
  have hA : ActiveAt G r a A := by
    by_contra h
    simp [GammaAB,h] at hcard
    omega
  obtain ⟨W,hW,hatt,hc⟩ := exists_attached_subset_card (gamma_attached G r a b A hA) k hcard
  refine ⟨W,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,attached_to_mission G A W hatt,?_⟩,?_⟩⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hA v hv
    · exact (gamma_active G r a b A hA (hW hv)).2.1
  · intro v hv
    exact (gamma_active G r a b A hA (hW hv)).2.2
lemma boundary_choose_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (a : ℝ) (b : WithTop ℝ) (A : Finset V) (k : ℕ) (hk : 1≤k) :
    (KAB G r a b A).choose k ≤ (retained G A k a b r).card := by
  by_cases hA : ActiveAt G r a A
  · let B := (outerBdry G A).filter (fun v=>a≤tau G r v ∧ (r v:WithTop ℝ)<b)
    have hsub : B.powersetCard k ⊆ retained G A k a b r := by
      intro W hW
      obtain ⟨hWB,hc⟩ := Finset.mem_powersetCard.mp hW
      have hm (v : V) (hv : v∈W) : v∉A ∧ (∃x∈A,G.Adj x v) ∧ a≤tau G r v ∧ (r v:WithTop ℝ)<b := by
        have hh := hWB hv
        simpa only [B,Finset.mem_filter,outerBdry,Finset.mem_univ,true_and,and_assoc] using hh
      have hatt : Attached G A W := by
        refine ⟨Finset.disjoint_left.mpr (fun v hvA hv=>(hm v hv).1 hvA),?_⟩
        intro v hv
        obtain ⟨x,hx,hxv⟩ := (hm v hv).2.1
        exact ⟨x,hx,Relation.ReflTransGen.single ⟨hxv,Finset.mem_union_right A hv⟩⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,attached_to_mission G A W hatt,?_⟩,?_⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact hA v hv
        · exact (hm v hv).2.2.1
      · intro v hv
        exact (hm v hv).2.2.2
    simpa only [KAB,if_pos hA,Finset.card_powersetCard,B] using Finset.card_le_card hsub
  · simp [KAB,hA,Nat.choose_eq_zero_of_lt (show 0<k from hk)]
end ExtensionCertificates

-- Source: Solutions.PermutationSymmetry
namespace ArrivalSymmetry
open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Relabel independent rank coordinates by a finite permutation. -/
def coordinatePermutation (σ : Equiv.Perm V) : (V → ℝ) ≃ᵐ (V → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) σ.symm

@[simp] theorem coordinatePermutation_apply (σ : Equiv.Perm V) (r : V → ℝ) (v : V) :
    coordinatePermutation σ r v = r (σ v) := by
  simp [coordinatePermutation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem coordinatePermutation_measurePreserving (σ : Equiv.Perm V) :
    MeasurePreserving (coordinatePermutation σ)
      (Measure.pi (fun _ : V => μ))
      (Measure.pi (fun _ : V => μ)) :=
  measurePreserving_piCongrLeft (fun _ : V => μ) σ.symm

theorem integral_coordinatePermutation (σ : Equiv.Perm V) (F : (V → ℝ) → ℝ) :
    (∫ r, F (coordinatePermutation σ r) ∂Measure.pi (fun _ => μ)) =
      ∫ r, F r ∂Measure.pi (fun _ => μ) :=
  (coordinatePermutation_measurePreserving μ σ).integral_comp
    (coordinatePermutation σ).measurableEmbedding F

/-- Pointwise uniform average over all coordinate permutations. -/
noncomputable def permutationAverage (F : (V → ℝ) → ℝ) (r : V → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm V, F (coordinatePermutation σ r)) / Fintype.card (Equiv.Perm V)

theorem integral_permutationAverage (F : (V → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : V => μ))) :
    (∫ r, permutationAverage F r ∂Measure.pi (fun _ => μ)) =
      ∫ r, F r ∂Measure.pi (fun _ => μ) := by
  have hcomp (σ : Equiv.Perm V) :
      Integrable (fun r => F (coordinatePermutation σ r))
        (Measure.pi (fun _ : V => μ)) :=
    ((coordinatePermutation_measurePreserving μ σ).integrable_comp hF.aestronglyMeasurable).mpr hF
  unfold permutationAverage
  rw [integral_div, integral_finsetSum _ (fun σ _ => hcomp σ)]
  simp_rw [integral_coordinatePermutation μ]
  have hn : (Fintype.card (Equiv.Perm V) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn

/-- Averaging over permutations may be replaced by an a.e. identified statistic. -/
theorem integral_eq_of_permutationAverage_ae (F H : (V → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : V => μ)))
    (havg : permutationAverage F =ᵐ[Measure.pi (fun _ : V => μ)] H) :
    (∫ r, F r ∂Measure.pi (fun _ => μ)) =
      ∫ r, H r ∂Measure.pi (fun _ => μ) := by
  rw [← integral_permutationAverage μ F hF]
  exact integral_congr_ae havg

/-- Finite-range expectation written using the actual masses of its level sets. -/
theorem integral_comp_nat_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → ℕ) (hK : Measurable K)
    (n : ℕ) (hKn : ∀ ω, K ω ≤ n) (g : ℕ → ℝ) :
    (∫ ω, g (K ω) ∂μ) =
      ∑ j ∈ Finset.range (n + 1), μ.real {ω | K ω = j} * g j := by
  classical
  have heq (ω : Ω) : g (K ω) =
      ∑ j ∈ Finset.range (n + 1), if K ω = j then g j else 0 := by
    simp [eq_comm, Finset.mem_range.mpr (Nat.lt_succ_of_le (hKn ω))]
  have hmeas (j : ℕ) : MeasurableSet {ω | K ω = j} :=
    (hK.eq measurable_const).setOf
  have hf (j : ℕ) : (fun ω => if K ω = j then g j else 0) =
      ({ω | K ω = j}).indicator (fun _ => g j) := by
    funext ω
    simp [Set.indicator]
  have hint (j : ℕ) : Integrable (fun ω => if K ω = j then g j else 0) μ := by
    rw [hf]
    exact (integrable_const (μ := μ) (g j)).indicator (hmeas j)
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hf]
  rw [integral_indicator (hmeas j), integral_const]
  simp [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]


end ArrivalSymmetry

-- Source: Solutions.ArrivalOrder
open MeasureTheory ProbabilityTheory
namespace ArrivalOrder
open Classical ExponentialArrivals ArrivalSymmetry
/-- Number of raw coordinates strictly below a threshold. -/
noncomputable def rankArrivalCount {V : Type*} [Fintype V] (raw : V → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun v => raw v < t).card

theorem rankArrivalCount_le {V : Type*} [Fintype V] (raw : V → ℝ) (t : ℝ) :
    rankArrivalCount raw t ≤ Fintype.card V := Finset.card_le_univ _

/-- The increasing enumeration of an injective finite rank assignment. -/
noncomputable def sortedRankEquiv {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) : Fin n ≃ V := by
  letI := LinearOrder.lift' raw hinj
  exact (Fintype.orderIsoFinOfCardEq V (by simpa using Fintype.card_congr e.symm)).toEquiv

theorem sortedRankEquiv_strictMono {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) :
    StrictMono (fun i => raw (sortedRankEquiv e raw hinj i)) := by
  letI := LinearOrder.lift' raw hinj
  exact (Fintype.orderIsoFinOfCardEq V
    (by simpa using Fintype.card_congr e.symm)).strictMono

theorem rankArrivalCount_le_of_equiv {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (t : ℝ) : rankArrivalCount raw t ≤ n := by
  have hcard : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  simpa [hcard] using rankArrivalCount_le raw t

/-- In increasing rank order, precisely the first `rankArrivalCount` positions have arrived. -/
theorem sortedRankEquiv_lt_iff {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) (t : ℝ) (i : Fin n) :
    i.val < rankArrivalCount raw t ↔ raw (sortedRankEquiv e raw hinj i) < t := by
  have hcard : (Finset.univ.filter fun j : Fin n =>
      raw (sortedRankEquiv e raw hinj j) < t).card = rankArrivalCount raw t := by
    apply Finset.card_equiv (sortedRankEquiv e raw hinj)
    intro j
    simp
  rw [← hcard]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  exact ((sortedRankEquiv_strictMono e raw hinj).monotone hba).trans_lt ha


section
variable {V : Type*} [Fintype V]
theorem ae_rawRanks_distinct {v w : V} (hvw : v ≠ w) :
    ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ => (expMeasure 1)), r v ≠ r w := by
  have hind : IndepFun (fun r : V → ℝ => r v) (fun r : V → ℝ => r w)
      (Measure.pi (fun _ => (expMeasure 1))) :=
    (iIndepFun_pi (μ := fun _ : V => (expMeasure 1))
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hvw
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply v).aemeasurable (measurable_pi_apply w).aemeasurable
  rw [(measurePreserving_eval (fun _ : V => (expMeasure 1)) v).map_eq,
    (measurePreserving_eval (fun _ : V => (expMeasure 1)) w).map_eq] at hmap
  have hpair : ∀ᵐ z ∂(expMeasure 1).prod (expMeasure 1), z.1 ≠ z.2 := by
    rw [ae_iff]
    simp only [not_not]
    apply Measure.measure_prod_null_of_ae_null
    · exact measurableSet_eq_fun
        (measurable_fst : Measurable (fun z : ℝ × ℝ => z.1)) measurable_snd
    · filter_upwards [] with x
      change (expMeasure 1) {y : ℝ | x = y} = 0
      simp
  apply ae_of_ae_map (μ := Measure.pi (fun _ : V => (expMeasure 1)))
    (f := fun r : V → ℝ => (r v, r w)) (p := fun z : ℝ × ℝ => z.1 ≠ z.2)
    ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable
  rw [hmap]
  exact hpair

theorem ae_rawRanks_injective :
    ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ => (expMeasure 1)), Function.Injective r := by
  apply Filter.eventually_all.mpr
  intro v
  apply Filter.eventually_all.mpr
  intro w
  by_cases h : v = w
  · exact Filter.Eventually.of_forall (fun _ _ => h)
  · filter_upwards [ae_rawRanks_distinct h] with r hr heq
    exact (hr heq).elim


end
end ArrivalOrder

-- Source: Solutions.ArrivalPolynomial
namespace ArrivalPolynomial
open scoped BigOperators
open Set

noncomputable def arrivalWeight (n j : ℕ) (t : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n j).eval t

theorem arrivalWeight_formula (n j : ℕ) (t : ℝ) :
    arrivalWeight n j t = (n.choose j : ℝ) * t ^ j * (1 - t) ^ (n - j) := by
  simp [arrivalWeight, bernsteinPolynomial]

theorem arrivalWeight_nonneg (n j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ arrivalWeight n j t := by
  rw [arrivalWeight_formula]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)

theorem arrivalWeight_sum (n : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (n + 1), arrivalWeight n j t) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.eval t) (bernsteinPolynomial.sum ℝ n)
  simpa [arrivalWeight, Polynomial.eval_finsetSum] using h

theorem arrivalWeight_eq_zero_of_lt (n j : ℕ) (t : ℝ) (h : n < j) :
    arrivalWeight n j t = 0 := by
  simp [arrivalWeight, bernsteinPolynomial.eq_zero_of_lt ℝ h]

theorem hasDerivAt_arrivalWeight_zero (n : ℕ) (t : ℝ) :
    HasDerivAt (arrivalWeight n 0) (-(n : ℝ) * arrivalWeight (n - 1) 0 t) t := by
  have h := (bernsteinPolynomial ℝ n 0).hasDerivAt t
  rw [bernsteinPolynomial.derivative_zero] at h
  convert! h using 1
  simp [arrivalWeight]

theorem hasDerivAt_arrivalWeight_succ (n j : ℕ) (t : ℝ) :
    HasDerivAt (arrivalWeight (n + 1) (j + 1))
      (((n : ℝ) + 1) * (arrivalWeight n j t - arrivalWeight n (j + 1) t)) t := by
  have h := (bernsteinPolynomial ℝ (n + 1) (j + 1)).hasDerivAt t
  rw [bernsteinPolynomial.derivative_succ_aux] at h
  convert! h using 1
  simp [arrivalWeight]

noncomputable def arrivalMixture (n : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * g j

/-- The derivative is the Bernstein mixture of successive differences. -/
theorem hasDerivAt_arrivalMixture_succ (n : ℕ) (g : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (arrivalMixture (n + 1) g)
      (((n : ℝ) + 1) *
        ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * (g (j + 1) - g j)) t := by
  have htail : HasDerivAt
      (fun t ↦ ∑ j ∈ Finset.range (n + 1), arrivalWeight (n + 1) (j + 1) t * g (j + 1))
      (∑ j ∈ Finset.range (n + 1),
        (((n : ℝ) + 1) * (arrivalWeight n j t - arrivalWeight n (j + 1) t)) * g (j + 1)) t := by
    convert! HasDerivAt.sum
      (fun j (_hj : j ∈ Finset.range (n + 1)) ↦
        (hasDerivAt_arrivalWeight_succ n j t).mul_const (g (j + 1))) using 1
    ext x
    simp only [Finset.sum_apply]
  have hhead := (hasDerivAt_arrivalWeight_zero (n + 1) t).mul_const (g 0)
  have htotal := htail.add hhead
  have hshift :
      (∑ j ∈ Finset.range (n + 1), arrivalWeight n (j + 1) t * g (j + 1)) +
        arrivalWeight n 0 t * g 0 =
      ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * g j := by
    rw [← Finset.sum_range_succ' (fun j ↦ arrivalWeight n j t * g j) (n + 1),
      Finset.sum_range_succ]
    rw [arrivalWeight_eq_zero_of_lt n (n + 1) t (Nat.lt_succ_self n)]
    ring
  convert! htotal using 1
  · ext x
    exact Finset.sum_range_succ' (fun j ↦ arrivalWeight (n + 1) j x * g j) (n + 1)
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    have hm := congrArg (fun z : ℝ ↦ ((n : ℝ) + 1) * z) hshift
    nlinarith

/-- The change from `n-1` to `n` Bernstein weights is exactly the number of
unarrived coordinates times the remaining-time factor. -/
theorem arrivalWeight_step_identity (n j : ℕ) (t : ℝ) (hj : j ≤ n) :
    ((n + 1 - j : ℕ) : ℝ) * arrivalWeight (n + 1) j t =
      ((n : ℝ) + 1) * (1 - t) * arrivalWeight n j t := by
  have hchoose : ((n + 1 - j : ℕ) : ℝ) * ((n + 1).choose j : ℝ) =
      ((n : ℝ) + 1) * (n.choose j : ℝ) := by
    have h := congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.choose_mul_succ_eq n j)
    push_cast at h
    nlinarith [h]
  have hsub : n + 1 - j = (n - j) + 1 := by omega
  rw [arrivalWeight_formula, arrivalWeight_formula, hsub, pow_succ]
  calc
    _ = (((n - j + 1 : ℕ) : ℝ) * ((n + 1).choose j : ℝ)) *
        (t ^ j * (1 - t) ^ (n - j) * (1 - t)) := by ring
    _ = (((n : ℝ) + 1) * (n.choose j : ℝ)) *
        (t ^ j * (1 - t) ^ (n - j) * (1 - t)) := by rw [← hsub, hchoose]
    _ = _ := by ring

noncomputable def arrivalDrift (n : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, arrivalWeight n j t * ((n - j : ℕ) : ℝ) * (g j - g (j + 1))

/-- The actual derivative identity in arrival-hazard form. -/
theorem hasDerivAt_arrivalMixture (n : ℕ) (g : ℕ → ℝ) (t : ℝ)
    (hn : 0 < n) (ht : t ≠ 1) :
    HasDerivAt (arrivalMixture n g) (-arrivalDrift n g t / (1 - t)) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  convert! hasDerivAt_arrivalMixture_succ m g t using 1
  dsimp [arrivalDrift]
  rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hweight := arrivalWeight_step_identity m j t (by simp only [Finset.mem_range] at hj; omega)
  have htne : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply (div_eq_iff htne).mpr
  have hm := congrArg (fun z : ℝ ↦ z * (g j - g (j + 1))) hweight
  nlinarith [hm]


end ArrivalPolynomial

-- Source: Solutions.OrderMixture
open MeasureTheory ProbabilityTheory
namespace OrderMixture
open Classical ArrivalSymmetry ArrivalOrder ExponentialArrivals ArrivalPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
noncomputable def representative (e : Fin n ≃ V) (σ : Equiv.Perm V) : V → ℝ :=
  fun v => ((e.symm (σ v)).val : ℝ)
noncomputable def profile (e : Fin n ≃ V) (H : ℝ → (V → ℝ) → ℝ) (j : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm V, H (j : ℝ) (representative e σ)) / Fintype.card (Equiv.Perm V)

def PrefixInvariant (H : ℝ → (V → ℝ) → ℝ) : Prop :=
  ∀ r q s t,
    (∀ v, r v < s ↔ q v < t) →
    (∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) →
    H s r = H t q

theorem permutation_average_eq_profile (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (r : V → ℝ) (hr : Function.Injective r) (s : ℝ) :
    permutationAverage (H s) r = profile e H (rankArrivalCount r s) := by
  let q := sortedRankEquiv e r hr
  let K : Equiv.Perm V := q.symm.trans e
  have hv (σ : Equiv.Perm V) : H s (coordinatePermutation σ r) =
      H (rankArrivalCount r s : ℝ) (representative e (K * σ)) := by
    apply hH
    · intro v
      have hi : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have h := sortedRankEquiv_lt_iff e r hr s (q.symm (σ v))
      have he : sortedRankEquiv e r hr (q.symm (σ v)) = σ v := q.apply_symm_apply _
      rw [he] at h
      exact h.symm.trans (by simp)
    · intro v w hv hw
      have hi (v : V) : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have hmono : StrictMono (fun i => r (q i)) := sortedRankEquiv_strictMono e r hr
      have hh := hmono.lt_iff_lt (a := q.symm (σ v)) (b := q.symm (σ w))
      simpa only [Equiv.apply_symm_apply,Fin.lt_def,Nat.cast_lt] using hh
  unfold permutationAverage profile
  simp_rw [hv]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft K)
  intro σ
  rfl

/-- A prefix-invariant statistic has a finite binomial-mixture expectation.
This is the exact permutation argument, with no conditioning on null events. -/
theorem expectation_eq_mixture (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (s : ℝ) (hs : 0 ≤ s)
    (hInt : Integrable (H s) (Measure.pi (fun _ : V => expMeasure 1))) :
    (∫ r, H s r ∂Measure.pi (fun _ : V => expMeasure 1)) =
      arrivalMixture n (profile e H) (1 - Real.exp (-s)) := by
  have havg : permutationAverage (H s) =ᵐ[Measure.pi (fun _ : V => expMeasure 1)]
      (fun r => profile e H (rankArrivalCount r s)) := by
    filter_upwards [ae_rawRanks_injective (V := V)] with r hr
    exact permutation_average_eq_profile e H hH r hr s
  rw [integral_eq_of_permutationAverage_ae (expMeasure 1) (H s) _ hInt havg]
  rw [integral_comp_nat_bounded _ (fun r => rankArrivalCount r s)
    (measurable_retainedVertices_card Finset.univ s) n
    (fun r => rankArrivalCount_le_of_equiv e r s)]
  unfold arrivalMixture
  apply Finset.sum_congr rfl
  intro j hj
  have hc : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  have hm := measureReal_retainedVertices_card (V := V) Finset.univ j s hs
  simpa only [rankArrivalCount,retainedVertices,Finset.card_univ,hc,
    arrivalWeight_formula,sub_sub_cancel] using congrArg (fun x : ℝ => x * profile e H j) hm
end OrderMixture

-- Source: Solutions.NonnegativeOrderMixture
open MeasureTheory ProbabilityTheory
namespace NonnegativeOrderMixture
open Classical ArrivalSymmetry ArrivalOrder ExponentialArrivals ArrivalPolynomial OrderMixture
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
def PrefixInvariant (H : ℝ → (V → ℝ) → ℝ) : Prop :=
  ∀ r q s t,
    (∀ v, 0 ≤ r v) → (∀ v, 0 ≤ q v) → 0 ≤ s → 0 ≤ t →
    (∀ v, r v < s ↔ q v < t) →
    (∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) →
    H s r = H t q

theorem permutation_average_eq_profile (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (r : V → ℝ) (hr : Function.Injective r) (hr0 : ∀ v, 0 ≤ r v) (s : ℝ) (hs : 0 ≤ s) :
    permutationAverage (H s) r = profile e H (rankArrivalCount r s) := by
  let q := sortedRankEquiv e r hr
  let K : Equiv.Perm V := q.symm.trans e
  have hv (σ : Equiv.Perm V) : H s (coordinatePermutation σ r) =
      H (rankArrivalCount r s : ℝ) (representative e (K * σ)) := by
    apply hH
    · intro v
      simpa only [coordinatePermutation_apply] using hr0 (σ v)
    · intro v
      exact Nat.cast_nonneg _
    · exact hs
    · exact Nat.cast_nonneg _
    · intro v
      have hi : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have h := sortedRankEquiv_lt_iff e r hr s (q.symm (σ v))
      have he : sortedRankEquiv e r hr (q.symm (σ v)) = σ v := q.apply_symm_apply _
      rw [he] at h
      exact h.symm.trans (by simp)
    · intro v w hv hw
      have hi (v : V) : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have hmono : StrictMono (fun i => r (q i)) := sortedRankEquiv_strictMono e r hr
      have hh := hmono.lt_iff_lt (a := q.symm (σ v)) (b := q.symm (σ w))
      simpa only [Equiv.apply_symm_apply,Fin.lt_def,Nat.cast_lt] using hh
  unfold permutationAverage profile
  simp_rw [hv]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft K)
  intro σ
  rfl

lemma ae_nonnegative : ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ : V => expMeasure 1), ∀ v, 0 ≤ r v := by
  have hscalar : ∀ᵐ x : ℝ ∂expMeasure 1, 0 ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    change expMeasure 1 (Set.Iio 0) = 0
    rw [← ofReal_measureReal,expOne_real_Iio 0 le_rfl]
    simp
  apply Filter.eventually_all.mpr
  intro v
  apply ae_of_ae_map (μ := Measure.pi (fun _ : V => expMeasure 1))
    (f := fun r : V → ℝ => r v) (p := fun x : ℝ => 0 ≤ x) (measurable_pi_apply v).aemeasurable
  rw [(measurePreserving_eval (fun _ : V => expMeasure 1) v).map_eq]
  exact hscalar

/-- A prefix-invariant statistic has a finite binomial-mixture expectation.
This is the exact permutation argument, with no conditioning on null events. -/
theorem expectation_eq_mixture (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (s : ℝ) (hs : 0 ≤ s)
    (hInt : Integrable (H s) (Measure.pi (fun _ : V => expMeasure 1))) :
    (∫ r, H s r ∂Measure.pi (fun _ : V => expMeasure 1)) =
      arrivalMixture n (profile e H) (1 - Real.exp (-s)) := by
  have havg : permutationAverage (H s) =ᵐ[Measure.pi (fun _ : V => expMeasure 1)]
      (fun r => profile e H (rankArrivalCount r s)) := by
    filter_upwards [ae_rawRanks_injective (V := V),ae_nonnegative (V := V)] with r hr hr0
    exact permutation_average_eq_profile e H hH r hr hr0 s hs
  rw [integral_eq_of_permutationAverage_ae (expMeasure 1) (H s) _ hInt havg]
  rw [integral_comp_nat_bounded _ (fun r => rankArrivalCount r s)
    (measurable_retainedVertices_card Finset.univ s) n
    (fun r => rankArrivalCount_le_of_equiv e r s)]
  unfold arrivalMixture
  apply Finset.sum_congr rfl
  intro j hj
  have hc : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  have hm := measureReal_retainedVertices_card (V := V) Finset.univ j s hs
  simpa only [rankArrivalCount,retainedVertices,Finset.card_univ,hc,
    arrivalWeight_formula,sub_sub_cancel] using congrArg (fun x : ℝ => x * profile e H j) hm
end NonnegativeOrderMixture

-- Source: Solutions.PrefixOrderActivity
open RGMISFast
namespace PrefixOrderActivity
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma activity_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (hlow : ∀ v, r v < s ↔ q v < t)
    (hord : ∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) (v : V) :
    s ≤ tau G r v ↔ t ≤ tau G q v := by
  have hm : ∀ w, r w < s → inMIS G r w = inMIS G q w := by
    intro w
    induction w using (measure (rk r)).wf.induction with
    | h w ih =>
      intro hw
      have hh : inMIS G r w = true ↔ inMIS G q w = true := by
        rw [mis_true_iff,mis_true_iff]
        constructor
        · intro h z ha hz
          have hzs : q z < t := hz.trans ((hlow w).mp hw)
          have hzr := (hlow z).mpr hzs
          have hzw := (hord z w hzr hw).mpr hz
          rw [← ih z (rk_lt r hzw) hzr]
          exact h z ha hzw
        · intro h z ha hz
          have hzs := hz.trans hw
          rw [ih z (rk_lt r hz) hzs]
          exact h z ha ((hord z w hzs hw).mp hz)
      cases hr : inMIS G r w <;> cases hq : inMIS G q w <;> simp_all
  rw [active_vertex_iff,active_vertex_iff]
  constructor
  · intro h w ha hqw
    by_contra hs
    have hwr := (hlow w).mpr (lt_of_not_ge hs)
    have hrw : inMIS G r w = true := (hm w hwr).trans hqw
    exact (not_le_of_gt hwr) (h w ha hrw)
  · intro h w ha hrw
    by_contra hs
    have hwr := lt_of_not_ge hs
    have hqw : inMIS G q w = true := (hm w hwr).symm.trans hrw
    exact (not_le_of_gt ((hlow w).mp hwr)) (h w ha hqw)

lemma Y_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) (u : V) (k : ℕ) :
    Y G u k s r = Y G u k t q := by
  classical
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro A hA
  have ha : ActiveAt G r s A ↔ ActiveAt G q t A := by
    unfold ActiveAt
    simp_rw [h]
  rw [ha]
lemma dsSum_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) (u : V) (k : ℕ) :
    dsSum G u k s r = dsSum G u k t q := by
  classical
  have hc : countedW G u k s r = countedW G u k t q := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    have ha : ActiveAt G r s (insert u W) ↔ ActiveAt G q t (insert u W) := by
      unfold ActiveAt
      simp_rw [h]
    rw [ha]
  have he : {v | s ≤ tau G r v} = {v | t ≤ tau G q v} := Set.ext h
  unfold dsSum
  rw [hc,he]
end PrefixOrderActivity

-- Source: Solutions.HistoryExtensionProfile
open MeasureTheory ProbabilityTheory RGMISFast
namespace HistoryExtensionProfile
open Classical ExponentialArrivals ExtensionCounts
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V]
noncomputable def join (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (b r : V → ℝ) : V → ℝ :=
  fun v => if r₀ v < θ then r₀ v else if v ∈ A then b v else θ+r v
noncomputable def process (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (s : ℝ) (r : V → ℝ) : V → ℝ :=
  join r₀ θ A (fun _ => θ+s) r
lemma join_measurable (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (b : V → ℝ) :
    Measurable (join r₀ θ A b) := by
  apply measurable_pi_lambda
  intro v
  unfold join
  split_ifs <;> fun_prop
lemma join_map (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (b : V → ℝ) :
    (Measure.pi (fun _ : V => expMeasure 1)).map (join r₀ θ A b) = condLaw r₀ θ A b := by
  have hm (v : V) : Measurable (fun x : ℝ => if r₀ v < θ then r₀ v else if v ∈ A then b v else θ+x) := by
    split_ifs <;> fun_prop
  unfold join
  rw [Measure.pi_map_pi (fun v => (hm v).aemeasurable)]
  unfold condLaw
  congr 1
  funext v
  by_cases hv : r₀ v < θ <;> by_cases ha : v ∈ A <;> simp [hv,ha]

lemma replace_pins_activity (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (b c r : V → ℝ) (t : ℝ)
    (hb : ∀ v ∈ A, t ≤ b v) (hc : ∀ v ∈ A, t ≤ c v) (v : V) :
    t ≤ tau G (join r₀ θ A b r) v ↔ t ≤ tau G (join r₀ θ A c r) v := by
  apply PinnedActivity.activity_prefix_congr
  · intro w
    by_cases hw : r₀ w < θ
    · simp only [join,if_pos hw]
    · by_cases ha : w ∈ A
      · simp only [join,if_neg hw,if_pos ha]
        exact iff_of_false (not_lt_of_ge (hb w ha)) (not_lt_of_ge (hc w ha))
      · simp only [join,if_neg hw,if_neg ha]
  · intro w hw
    by_cases he : r₀ w < θ
    · simp only [join,if_pos he]
    · by_cases ha : w ∈ A
      · simp only [join,if_neg he,if_pos ha] at hw
        exact False.elim ((not_lt_of_ge (hb w ha)) hw)
      · simp only [join,if_neg he,if_neg ha]

lemma process_activity_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (r q : V → ℝ) (s t : ℝ)
    (hr : ∀ v, 0 ≤ r v) (hq : ∀ v, 0 ≤ q v) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hlow : ∀ v, r v < s ↔ q v < t)
    (hord : ∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) (v : V) :
    θ+s ≤ tau G (process r₀ θ A s r) v ↔ θ+t ≤ tau G (process r₀ θ A t q) v := by
  apply PrefixOrderActivity.activity_congr
  · intro w
    by_cases he : r₀ w < θ
    · simp only [process,join,if_pos he]
      constructor <;> intro h <;> linarith
    · by_cases ha : w ∈ A
      · simp only [process,join,if_neg he,if_pos ha,lt_self_iff_false]
      · simpa only [process,join,if_neg he,if_neg ha,add_lt_add_iff_left] using hlow w
  · intro w z hw hz
    have hwA : ¬r₀ w < θ → w ∉ A := by
      intro he ha
      simp only [process,join,if_neg he,if_pos ha,lt_self_iff_false] at hw
    have hzA : ¬r₀ z < θ → z ∉ A := by
      intro he ha
      simp only [process,join,if_neg he,if_pos ha,lt_self_iff_false] at hz
    by_cases hew : r₀ w < θ <;> by_cases hez : r₀ z < θ
    · simp only [process,join,if_pos hew,if_pos hez]
    · simp only [process,join,if_pos hew,if_neg hez,if_neg (hzA hez)]
      constructor <;> intro h <;> linarith [hr z,hq z]
    · simp only [process,join,if_neg hew,if_neg (hwA hew),if_pos hez]
      constructor <;> intro h <;> exfalso <;> linarith [hr w,hq w]
    · simp only [process,join,if_neg hew,if_neg hez,if_neg (hwA hew),if_neg (hzA hez),add_lt_add_iff_left] at hw hz ⊢
      exact hord w z hw hz

noncomputable def countProfile (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (s : ℝ) (r : V → ℝ) : ℝ :=
  Ncount G A k (θ+s) (process r₀ θ A s r)
noncomputable def lossProfile (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (s : ℝ) (r : V → ℝ) : ℝ :=
  loss G A k (θ+s) (process r₀ θ A s r)
lemma count_prefix_invariant (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) :
    NonnegativeOrderMixture.PrefixInvariant (countProfile G r₀ θ A k) := by
  intro r q s t hr hq hs ht hlo hord
  unfold countProfile
  simp only [count_eq_card]
  congr 2
  exact family_congr G A k _ _ _ _ (process_activity_congr G r₀ θ A r q s t hr hq hs ht hlo hord)
lemma loss_prefix_invariant (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) :
    NonnegativeOrderMixture.PrefixInvariant (lossProfile G r₀ θ A k) := by
  intro r q s t hr hq hs ht hlo hord
  unfold lossProfile
  congr 1
  exact loss_congr G A k _ _ _ _ (process_activity_congr G r₀ θ A r q s t hr hq hs ht hlo hord)

lemma loss_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (s : ℝ) :
    Measurable (fun r : V → ℝ => loss G A k s r) := by
  apply measurable_of_activity G s
  intro r q h
  exact loss_congr G A k s s r q h
lemma count_real_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (s : ℝ) :
    Measurable (fun r : V → ℝ => (Ncount G A k s r : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (Ncount_measurable_complete G A k s)
lemma loss_real_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (s : ℝ) :
    Measurable (fun r : V → ℝ => (loss G A k s r : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (loss_measurable G A k s)
lemma loss_bound (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    loss G A k s r ≤ Fintype.card (Finset V) * Fintype.card V := by
  calc
    _ ≤ ∑ _W ∈ family G A k s r, Fintype.card V := Finset.sum_le_sum (fun W _ => Finset.card_le_univ _)
    _ = (family G A k s r).card * Fintype.card V := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
lemma count_integrable (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] : Integrable (countProfile G r₀ θ A k s) μ := by
  have hm : Measurable (countProfile G r₀ θ A k s) :=
    (count_real_measurable G A k (θ+s)).comp (join_measurable r₀ θ A _)
  apply Integrable.of_bound hm.aestronglyMeasurable (Fintype.card (Finset V) : ℝ)
  filter_upwards [] with r
  rw [countProfile,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.card_le_univ (α := Finset V) _)
lemma loss_integrable (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] : Integrable (lossProfile G r₀ θ A k s) μ := by
  have hm : Measurable (lossProfile G r₀ θ A k s) :=
    (loss_real_measurable G A k (θ+s)).comp (join_measurable r₀ θ A _)
  apply Integrable.of_bound hm.aestronglyMeasurable ((Fintype.card (Finset V) * Fintype.card V : ℕ) : ℝ)
  filter_upwards [] with r
  rw [lossProfile,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast loss_bound G A k (θ+s) _
end HistoryExtensionProfile

-- Source: Solutions.PermutationRankSwap
open Classical
namespace PermutationRankSwap
open OrderMixture
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
def swapRanks (e : Fin n ≃ V) (j l : Fin n) : Equiv.Perm V := Equiv.swap (e j) (e l)
lemma rank_swap_eq_below (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n)
    (hl : j ≤ l) (v : V) (hv : representative e σ v < (j.val : ℝ)) :
    representative e (swapRanks e j l * σ) v = representative e σ v := by
  have hpos : (e.symm (σ v)).val < j.val := by
    unfold representative at hv
    exact_mod_cast hv
  have ha : σ v ≠ e j := by intro h; simp only [h,Equiv.symm_apply_apply] at hpos; omega
  have hb : σ v ≠ e l := by intro h; simp only [h,Equiv.symm_apply_apply] at hpos; exact (not_lt_of_ge hl) hpos
  simp only [representative,Equiv.Perm.mul_apply,swapRanks,Equiv.swap_apply_of_ne_of_ne ha hb]
lemma rank_swap_low_iff (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n)
    (hl : j ≤ l) (v : V) :
    representative e σ v < (j.val : ℝ) ↔
      representative e (swapRanks e j l * σ) v < (j.val : ℝ) := by
  constructor
  · intro h
    rw [rank_swap_eq_below e σ j l hl v h]
    exact h
  · intro h
    have hh := rank_swap_eq_below e (swapRanks e j l * σ) j l hl v h
    have he : swapRanks e j l * (swapRanks e j l * σ) = σ := by
      ext w
      simp [swapRanks,Equiv.Perm.mul_apply]
    rw [he] at hh
    rwa [← hh] at h
lemma swap_next_rank (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n) :
    representative e (swapRanks e j l * σ) (σ.symm (e l)) = (j.val : ℝ) := by
  simp [representative,swapRanks,Equiv.Perm.mul_apply]
lemma rank_injective (e : Fin n ≃ V) (σ : Equiv.Perm V) :
    Function.Injective (representative e σ) := by
  intro v w h
  apply σ.injective
  apply e.symm.injective
  apply Fin.ext
  unfold representative at h
  exact_mod_cast h
lemma rank_interval_unique (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n) (v : V)
    (hv : (j.val : ℝ) ≤ representative e (swapRanks e j l * σ) v ∧
      representative e (swapRanks e j l * σ) v < (j.val : ℝ) + 1) : v = σ.symm (e l) := by
  apply rank_injective e (swapRanks e j l * σ)
  rw [swap_next_rank]
  unfold representative at hv ⊢
  have ha : j.val ≤ (e.symm ((swapRanks e j l * σ) v)).val := by exact_mod_cast hv.1
  have hb : (e.symm ((swapRanks e j l * σ) v)).val < j.val + 1 := by exact_mod_cast hv.2
  exact_mod_cast (show (e.symm ((swapRanks e j l * σ) v)).val = j.val by omega)
end PermutationRankSwap

-- Source: Solutions.HistoryPermutationTransition
open RGMISFast
namespace HistoryPermutationTransition
open Classical HistoryExtensionProfile OrderMixture PermutationRankSwap ExtensionCounts
open RGMISGeneral.Polynomial ArrivalAuxiliary
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
noncomputable def ranks (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V)
    (σ : Equiv.Perm V) : V → ℝ := join r₀ θ A (fun _ => θ+n) (representative e σ)
lemma activity_process_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (σ : Equiv.Perm V)
    (j : ℕ) (hj : j ≤ n) (v : V) :
    θ+j ≤ tau G (process r₀ θ A j (representative e σ)) v ↔
      θ+j ≤ tau G (ranks e r₀ θ A σ) v := by
  apply replace_pins_activity
  · intro w hw; exact le_rfl
  · intro w hw
    have h : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
lemma activity_before_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (σ : Equiv.Perm V)
    (j l : Fin n) (hl : j ≤ l) (v : V) :
    θ+j.val ≤ tau G (ranks e r₀ θ A σ) v ↔
      θ+j.val ≤ tau G (ranks e r₀ θ A (swapRanks e j l * σ)) v := by
  rw [← activity_process_ranks G e r₀ θ A σ j.val j.isLt.le v,
    ← activity_process_ranks G e r₀ θ A (swapRanks e j l * σ) j.val j.isLt.le v]
  apply process_activity_congr
  · intro w; exact Nat.cast_nonneg _
  · intro w; exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · exact rank_swap_low_iff e σ j l hl
  · intro w z hw hz
    rw [rank_swap_eq_below e σ j l hl w hw,rank_swap_eq_below e σ j l hl z hz]
lemma family_before_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (σ : Equiv.Perm V)
    (j l : Fin n) (hl : j ≤ l) :
    family G A k (θ+j.val) (ranks e r₀ θ A σ) =
      family G A k (θ+j.val) (ranks e r₀ θ A (swapRanks e j l * σ)) :=
  family_congr G A k _ _ _ _ (activity_before_swap G e r₀ θ A σ j l hl)

lemma next_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (σ : Equiv.Perm V)
    (j l : Fin n) (hl : j ≤ l) :
    family G A k (θ+j.val+1) (ranks e r₀ θ A (swapRanks e j l * σ)) =
      (family G A k (θ+j.val) (ranks e r₀ θ A σ)).filter
        (fun W => σ.symm (e l) ∉ killingArrivals
          (restrictTo G {v | θ+j.val ≤ tau G (ranks e r₀ θ A σ) v}) A W) := by
  let r := ranks e r₀ θ A (swapRanks e j l * σ)
  let x := σ.symm (e l)
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hn : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
  have hone : ∀ w, θ+j.val ≤ r w → r w < θ+j.val+1 → w = x := by
    intro w hw ht
    have he : ¬r₀ w < θ := by
      intro he
      simp only [r,ranks,join,if_pos he] at hw
      linarith
    have ha : w ∉ A := by
      intro ha
      simp only [r,ranks,join,if_neg he,if_pos ha] at ht
      linarith
    simp only [r,ranks,join,if_neg he,if_neg ha] at hw ht
    apply rank_interval_unique e σ j l w
    constructor <;> linarith
  have hc := family_before_swap G e r₀ θ A k σ j l hl
  have hg : {v | θ+j.val ≤ tau G (ranks e r₀ θ A σ) v} = {v | θ+j.val ≤ tau G r v} :=
    Set.ext (activity_before_swap G e r₀ θ A σ j l hl)
  by_cases hi : x ∈ A ∨ r₀ x < θ
  · have hnone : ∀ w, ¬ (θ+j.val ≤ r w ∧ r w < θ+j.val+1) := by
      intro w hw
      have he := hone w hw.1 hw.2
      rw [he] at hw
      by_cases hearly : r₀ x < θ
      · simp only [r,ranks,join,if_pos hearly] at hw
        linarith [hw.1]
      · have hxA := hi.resolve_right hearly
        simp only [r,ranks,join,if_neg hearly,if_pos hxA] at hw
        linarith [hw.2]
    have hsame : family G A k (θ+j.val+1) r = family G A k (θ+j.val) r :=
      family_congr G A k _ _ _ _ (fun v =>
        (activity_no_arrival G r (θ+j.val) (θ+j.val+1) (by linarith) hnone v).symm)
    change family G A k (θ+j.val+1) r = _
    rw [hsame,← hc]
    symm
    apply Finset.filter_eq_self.mpr
    intro W hW hk
    have ha := killing_active G A k (θ+j.val) (ranks e r₀ θ A σ) W hW x hk
    rcases hi with hxA | hearly
    · exact ha.1 hxA
    · have hh := active_le_rank G (ranks e r₀ θ A σ) (θ+j.val) x ha.2
      simp only [ranks,join,if_pos hearly] at hh
      linarith
  · have hxA : x ∉ A := fun h => hi (Or.inl h)
    have hearly : ¬r₀ x < θ := fun h => hi (Or.inr h)
    have hrx : r x = θ+j.val := by
      simp only [r,ranks,join,if_neg hearly,if_neg hxA]
      rw [swap_next_rank]
    have hx : θ+j.val ≤ r x ∧ r x < θ+j.val+1 := by rw [hrx]; constructor <;> linarith
    change family G A k (θ+j.val+1) r = _
    rw [family_single_arrival G A k r (θ+j.val) (θ+j.val+1) (by linarith) x hxA hx hone,
      ← hc,← hg]
end HistoryPermutationTransition

-- Source: Solutions.HistoryPermutationTotalLoss
open RGMISFast
namespace HistoryPermutationTotalLoss
open Classical HistoryExtensionProfile OrderMixture PermutationRankSwap HistoryPermutationTransition
open ExtensionCounts RGMISGeneral.Polynomial ArrivalLoss ArrivalAuxiliary
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
lemma killing_position (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k j : ℕ) (σ : Equiv.Perm V)
    (W : Finset V) (hW : W ∈ family G A k (θ+j) (ranks e r₀ θ A σ))
    (x : V) (hx : x ∈ killingArrivals (restrictTo G {v | θ+j ≤ tau G (ranks e r₀ θ A σ) v}) A W) :
    j ≤ (e.symm (σ x)).val := by
  have ha := killing_active G A k (θ+j) (ranks e r₀ θ A σ) W hW x hx
  have hh := active_le_rank G (ranks e r₀ θ A σ) (θ+j) x ha.2
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have he : ¬r₀ x < θ := by
    intro he
    simp only [ranks,join,if_pos he] at hh
    linarith
  simp only [ranks,join,if_neg he,if_neg ha.1,representative] at hh
  have hp : (j : ℝ) ≤ (e.symm (σ x)).val := by linarith
  exact_mod_cast hp
lemma total_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (σ : Equiv.Perm V) (j : Fin n) :
    (∑ l ∈ Finset.Ici j,
      ((Ncount G A k (θ+j.val) (ranks e r₀ θ A σ) : ℝ) -
        (Ncount G A k (θ+j.val+1) (ranks e r₀ θ A (swapRanks e j l * σ)) : ℝ))) =
      (ExtensionCounts.loss G A k (θ+j.val) (ranks e r₀ θ A σ) : ℝ) := by
  let F := family G A k (θ+j.val) (ranks e r₀ θ A σ)
  let kill := killingArrivals (restrictTo G {v | θ+j.val ≤ tau G (ranks e r₀ θ A σ) v}) A
  let R := Finset.univ.filter (fun x => j.val ≤ (e.symm (σ x)).val)
  have hkill : ∀ W ∈ F, kill W ⊆ R := by
    intro W hW x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,killing_position G e r₀ θ A k j.val σ W hW x hx⟩
  let decrement := fun x => (F.card : ℝ) - ((F.filter fun W => x ∉ kill W).card : ℝ)
  have hsum : (∑ l ∈ Finset.Ici j, decrement (σ.symm (e l))) = ∑ x ∈ R, decrement x := by
    apply Finset.sum_bij (fun l _ => σ.symm (e l))
    · intro l hl
      simpa [R] using (Finset.mem_Ici.mp hl)
    · intro l hl m hm he
      exact e.injective (σ.symm.injective he)
    · intro x hx
      refine ⟨e.symm (σ x), ?_, ?_⟩
      · simpa [R] using hx
      · simp
    · intro l hl
      rfl
  have htotal := sum_count_loss_eq_sum_killing_card F R kill hkill
  calc
    _ = ∑ l ∈ Finset.Ici j, decrement (σ.symm (e l)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [count_eq_card,count_eq_card,next_family G e r₀ θ A k σ j l (Finset.mem_Ici.mp hl)]
    _ = ∑ W ∈ F, ((kill W).card : ℝ) := hsum.trans htotal
    _ = _ := by simp only [ExtensionCounts.loss,Nat.cast_sum,F,kill]
lemma terminal_loss_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (σ : Equiv.Perm V) :
    ExtensionCounts.loss G A k (θ+n) (ranks e r₀ θ A σ) = 0 := by
  unfold ExtensionCounts.loss
  apply Finset.sum_eq_zero
  intro W hW
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := killing_position G e r₀ θ A k n σ W hW x hx
  exact (not_le_of_gt (e.symm (σ x)).isLt) hh
end HistoryPermutationTotalLoss

-- Source: Solutions.HistoryFiniteProfileDrift
open RGMISFast
namespace HistoryFiniteProfileDrift
open Classical HistoryExtensionProfile OrderMixture PermutationRankSwap HistoryPermutationTransition
open HistoryPermutationTotalLoss ArrivalPolynomial ExtensionCounts
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
lemma countProfile_eq_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k j : ℕ) (hj : j ≤ n) (σ : Equiv.Perm V) :
    countProfile G r₀ θ A k (j : ℝ) (representative e σ) = (Ncount G A k (θ+j) (ranks e r₀ θ A σ) : ℝ) := by
  unfold countProfile
  simp only [count_eq_card]
  congr 2
  exact family_congr G A k _ _ _ _ (activity_process_ranks G e r₀ θ A σ j hj)
lemma lossProfile_eq_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k j : ℕ) (hj : j ≤ n) (σ : Equiv.Perm V) :
    lossProfile G r₀ θ A k (j : ℝ) (representative e σ) = (loss G A k (θ+j) (ranks e r₀ θ A σ) : ℝ) := by
  unfold lossProfile
  congr 1
  exact loss_congr G A k _ _ _ _ (activity_process_ranks G e r₀ θ A σ j hj)
lemma profile_loss_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k j : ℕ) (hj : j < n) :
    profile e (lossProfile G r₀ θ A k) j = (n-j : ℕ) *
      (profile e (countProfile G r₀ θ A k) j - profile e (countProfile G r₀ θ A k) (j+1)) := by
  let ij : Fin n := ⟨j,hj⟩
  have hs (l : Fin n) :
      (∑ σ : Equiv.Perm V, (Ncount G A k (θ+j+1) (ranks e r₀ θ A (swapRanks e ij l * σ)) : ℝ)) =
        ∑ σ : Equiv.Perm V, (Ncount G A k (θ+j+1) (ranks e r₀ θ A σ) : ℝ) := by
    apply Fintype.sum_equiv (Equiv.mulLeft (swapRanks e ij l))
    intro σ
    rfl
  unfold profile
  simp_rw [lossProfile_eq_ranks G e r₀ θ A k j hj.le,
    countProfile_eq_ranks G e r₀ θ A k j hj.le,
    countProfile_eq_ranks G e r₀ θ A k (j+1) (Nat.succ_le_of_lt hj)]
  simp only [Nat.cast_add,Nat.cast_one,← add_assoc]
  have ht (σ : Equiv.Perm V) := total_loss G e r₀ θ A k σ ij
  simp only [ij] at ht
  simp_rw [← ht]
  rw [Finset.sum_comm]
  simp only [Finset.sum_sub_distrib]
  simp only [ij] at hs
  simp only [hs]
  simp only [Finset.sum_const,Fin.card_Ici,nsmul_eq_mul,ij]
  ring
lemma profile_loss_terminal (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) :
    profile e (lossProfile G r₀ θ A k) n = 0 := by
  unfold profile
  simp_rw [lossProfile_eq_ranks G e r₀ θ A k n le_rfl,terminal_loss_zero]
  simp
lemma loss_mixture_eq_drift (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (z : ℝ) :
    arrivalMixture n (profile e (lossProfile G r₀ θ A k)) z =
      arrivalDrift n (profile e (countProfile G r₀ θ A k)) z := by
  unfold arrivalMixture arrivalDrift
  rw [Finset.sum_range_succ,profile_loss_terminal]
  simp only [mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [profile_loss_identity G e r₀ θ A k j (Finset.mem_range.mp hj)]
  ring
end HistoryFiniteProfileDrift

-- Source: Solutions.ExtensionExpectationDrift
open MeasureTheory ProbabilityTheory RGMISFast
namespace HistoryExtensionProfile
open Classical
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma power_integrable (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (s p : ℝ) (hp : 0 ≤ p)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun r => countProfile G r₀ θ A k s r ^ p) μ := by
  have hm : Measurable (countProfile G r₀ θ A k s) :=
    (count_real_measurable G A k (θ+s)).comp (join_measurable r₀ θ A _)
  apply Integrable.of_bound ((Real.continuous_rpow_const hp).measurable.comp hm).aestronglyMeasurable
    ((Fintype.card (Finset V) : ℝ) ^ p)
  filter_upwards [] with r
  simp only [Function.comp_apply, countProfile]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hp
  exact_mod_cast (Finset.card_le_univ (α := Finset V) _)
lemma expectation_drift_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ] :
    (k : ℝ) / Real.exp 1 * (∫ r, countProfile G r₀ θ A k s r ∂μ) ^ (1+(k:ℝ)⁻¹) ≤
      ∫ r, lossProfile G r₀ θ A k s r ∂μ := by
  have hp : (0 : ℝ) ≤ 1+(k:ℝ)⁻¹ := by positivity
  have hj := (convexOn_rpow (show (1 : ℝ) ≤ 1+(k:ℝ)⁻¹ from le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _)))).map_integral_le
    (Real.continuous_rpow_const hp).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun r => (show (0 : ℝ) ≤ countProfile G r₀ θ A k s r from Nat.cast_nonneg _)))
    (count_integrable G r₀ θ A k s μ) (power_integrable G r₀ θ A k s _ hp μ)
  have hi := integral_mono ((power_integrable G r₀ θ A k s _ hp μ).const_mul ((k:ℝ)/Real.exp 1))
    (loss_integrable G r₀ θ A k s μ) (fun r => ExtensionCounts.loss_lower G A k hk (θ+s) (process r₀ θ A s r))
  rw [integral_const_mul] at hi
  exact (mul_le_mul_of_nonneg_left hj (by positivity)).trans hi
end HistoryExtensionProfile

-- Source: Solutions.ArrivalExpansionDerivative
set_option autoImplicit false

lemma arrival_expansion_derivative (n : ℕ) (coeff : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z : ℝ => ∑ j ∈ Finset.range (n+1), coeff j * Real.exp (-(j:ℝ)*z))
      (-(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))) s := by
  have hd (j : ℕ) : HasDerivAt
      (fun z : ℝ => coeff j * Real.exp (-(j:ℝ)*z))
      (coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) s := by
    simpa using (((hasDerivAt_id s).const_mul (-(j:ℝ))).exp.const_mul (coeff j))
  have hh := HasDerivAt.fun_sum (u := Finset.range (n+1)) (fun j _ => hd j)
  have he : (∑ j ∈ Finset.range (n+1), coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) =
      -(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he] at hh
  exact hh

lemma derivative_from_arrival_expansion (f d : ℝ → ℝ) (n : ℕ) (coeff : ℕ → ℝ)
    (t : ℝ)
    (hf : ∀ s ∈ Set.Icc 0 t, f s = ∑ j ∈ Finset.range (n+1), coeff j*Real.exp (-(j:ℝ)*s))
    (hd : ∀ s ∈ Set.Icc 0 t, d s = ∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))
    (s : ℝ) (hs : s ∈ Set.Ico 0 t) : HasDerivWithinAt f (-d s) (Set.Icc 0 t) s := by
  have hs' : s ∈ Set.Icc 0 t := ⟨hs.1,hs.2.le⟩
  rw [hd s hs']
  exact (arrival_expansion_derivative n coeff s).hasDerivWithinAt.congr_of_mem hf hs'

-- Source: Solutions.ExponentialPolynomial
open scoped BigOperators
namespace ArrivalPolynomial

lemma exponential_mixture_derivative (n : ℕ) (g : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z => arrivalMixture n g (1 - Real.exp (-z)))
      (-arrivalDrift n g (1 - Real.exp (-s))) s := by
  by_cases hn : n = 0
  · subst n
    simpa [arrivalMixture,arrivalWeight,bernsteinPolynomial,arrivalDrift] using
      (hasDerivAt_const s (g 0))
  · have hq : HasDerivAt (fun z : ℝ => 1 - Real.exp (-z)) (Real.exp (-s)) s := by
      simpa using ((hasDerivAt_id s).neg.exp.const_sub 1)
    have he := Real.exp_pos (-s)
    have hd := (hasDerivAt_arrivalMixture n g (1 - Real.exp (-s))
      (Nat.pos_of_ne_zero hn) (by linarith)).comp s hq
    convert! hd using 1 <;> field_simp <;> ring

/-- The permutation means are Bernstein coefficients. After substituting
1-exp(-s), conversion to monomials supplies the constant exponential coefficients
and simultaneously the weighted coefficients of the exact loss profile. -/
theorem exponential_mixture_expansion (n : ℕ) (g : ℕ → ℝ) :
    ∃ m : ℕ, ∃ coeff : ℕ → ℝ,
      (∀ s : ℝ, arrivalMixture n g (1 - Real.exp (-s)) =
        ∑ j ∈ Finset.range (m+1), coeff j * Real.exp (-(j:ℝ)*s)) ∧
      (∀ s : ℝ, arrivalDrift n g (1 - Real.exp (-s)) =
        ∑ j ∈ Finset.range (m+1), (j:ℝ)*coeff j * Real.exp (-(j:ℝ)*s)) := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (n+1),
    (bernsteinPolynomial ℝ n j).comp (1 - Polynomial.X) * Polynomial.C (g j)
  have hp (s : ℝ) : P.eval (Real.exp (-s)) = arrivalMixture n g (1 - Real.exp (-s)) := by
    simp [P,arrivalMixture,arrivalWeight,Polynomial.eval_finsetSum]
  have hf (s : ℝ) : arrivalMixture n g (1 - Real.exp (-s)) =
      ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Real.exp (-(j:ℝ)*s) := by
    rw [← hp,Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨P.natDegree,P.coeff,hf,?_⟩
  intro s
  have hd := exponential_mixture_derivative n g s
  have he : (fun z => arrivalMixture n g (1 - Real.exp (-z))) =
      (fun z => ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Real.exp (-(j:ℝ)*z)) := funext hf
  rw [he] at hd
  have hh := hd.unique (arrival_expansion_derivative P.natDegree P.coeff s)
  exact neg_injective hh
end ArrivalPolynomial

-- Source: Solutions.PrescribedExtensionDriftComplete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace HistoryExtensionProfile
open Classical
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma conditional_representation (G : SimpleGraph V) [DecidableRel G.Adj]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) (k : ℕ) (s : ℝ)
    (hrA : ∀ v ∈ A, θ+s ≤ rA v) :
    (∫⁻ r, (Ncount G A k (θ+s) r : ℝ≥0∞) ∂condLaw r₀ θ A rA) =
      ENNReal.ofReal (∫ r, countProfile G r₀ θ A k s r ∂Measure.pi (fun _ : V => expMeasure 1)) := by
  have hm : Measurable (fun r : V → ℝ => (Ncount G A k (θ+s) r : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (Ncount_measurable_complete G A k (θ+s))
  rw [← join_map r₀ θ A rA,lintegral_map hm (join_measurable r₀ θ A rA)]
  rw [ofReal_integral_eq_lintegral_ofReal (count_integrable G r₀ θ A k s _)
    (Filter.Eventually.of_forall (fun r => (show 0 ≤ countProfile G r₀ θ A k s r from Nat.cast_nonneg _)))]
  apply lintegral_congr
  intro r
  have he := ExtensionCounts.family_congr G A k (θ+s) (θ+s)
    (join r₀ θ A rA r) (process r₀ θ A s r)
    (replace_pins_activity G r₀ θ A rA (fun _ => θ+s) r (θ+s) hrA (fun _ _ => le_rfl))
  simp only [countProfile,ExtensionCounts.count_eq_card,ENNReal.ofReal_natCast]
  rw [he]
end HistoryExtensionProfile

open Classical HistoryExtensionProfile OrderMixture ArrivalPolynomial
set_option maxHeartbeats 1000000
theorem prescribed_extension_drift_complete {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (k : ℕ) (hk : 1 ≤ k) :
    ∃ f f' : ℝ → ℝ,
      (∀ s ∈ Set.Icc 0 (a-θ),
        (∫⁻ r, (Ncount G A k (θ+s) r : ℝ≥0∞) ∂(condLaw r₀ θ A rA)) = ENNReal.ofReal (f s)) ∧
      ContinuousOn f (Set.Icc 0 (a-θ)) ∧
      (∀ s ∈ Set.Icc 0 (a-θ), 0 ≤ f s) ∧
      (∀ s ∈ Set.Ioo 0 (a-θ), HasDerivAt f (f' s) s) ∧
      (∀ s ∈ Set.Ioo 0 (a-θ),
        f' s ≤ -(k:ℝ) / Real.exp 1 * f s ^ (1+(k:ℝ)⁻¹)) := by
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let g := profile e (countProfile G r₀ θ A k)
  let f : ℝ → ℝ := fun s => arrivalMixture n g (1-Real.exp (-s))
  let f' : ℝ → ℝ := fun s => -arrivalDrift n g (1-Real.exp (-s))
  have hf (s : ℝ) (hs : 0 ≤ s) :
      (∫ r, countProfile G r₀ θ A k s r ∂Measure.pi (fun _ : V => expMeasure 1)) = f s :=
    NonnegativeOrderMixture.expectation_eq_mixture e _ (count_prefix_invariant G r₀ θ A k) s hs
      (count_integrable G r₀ θ A k s _)
  have hd (s : ℝ) (hs : 0 ≤ s) :
      (∫ r, lossProfile G r₀ θ A k s r ∂Measure.pi (fun _ : V => expMeasure 1)) = -f' s := by
    rw [NonnegativeOrderMixture.expectation_eq_mixture e _ (loss_prefix_invariant G r₀ θ A k) s hs
      (loss_integrable G r₀ θ A k s _), HistoryFiniteProfileDrift.loss_mixture_eq_drift]
    simp [f',g]
  refine ⟨f,f',?_,?_,?_,?_,?_⟩
  · intro s hs
    rw [conditional_representation G r₀ θ A rA k s (fun v hv => by linarith [hrA v hv,hs.2]), hf s hs.1]
  · have hc : Continuous f := by
      dsimp [f,arrivalMixture,arrivalWeight]
      fun_prop
    exact hc.continuousOn
  · intro s hs
    rw [← hf s hs.1]
    exact integral_nonneg (fun r => Nat.cast_nonneg _)
  · intro s hs
    exact exponential_mixture_derivative n g s
  · intro s hs
    have hh := expectation_drift_bound G r₀ θ A k hk s (Measure.pi (fun _ : V => expMeasure 1))
    rw [hf s hs.1.le, hd s hs.1.le] at hh
    have h := neg_le_neg hh
    simpa only [neg_neg,neg_div,neg_mul] using h

-- Source: Solutions.PrescribedDecay
set_option autoImplicit false
namespace PrescribedDecay

open Set

/-- The negative inverse power converts the nonlinear differential inequality
into a lower bound on its derivative. -/
theorem inverse_power_derivative_lower (y v c : ℝ) (k : ℕ)
    (hy : 0 < y) (hk : 0 < k)
    (hv : v ≤ -(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) :
    c ≤ v * (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoeff : (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hkpos.le))
      (Real.rpow_nonneg hy.le _)
  have hmul := mul_le_mul_of_nonpos_right hv hcoeff
  have hidentity : (-(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) *
      ((-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) = c := by
    calc
      _ = (k : ℝ) * (k : ℝ)⁻¹ * c *
          (y ^ (1 + (k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) := by ring
      _ = c := by
        rw [← Real.rpow_add hy]
        have hexp : (1 + (k : ℝ)⁻¹) + (-(k : ℝ)⁻¹ - 1) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_inv_cancel₀ hkpos.ne']
        ring
  rw [hidentity] at hmul
  nlinarith [hmul]

/-- Integration with an arbitrary differentiable clock. This stronger form
retains the initial value and requires strict positivity of the function. -/
theorem inverse_power_clock_growth
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfpos : ∀ t ∈ Icc 0 a, 0 < f t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹)) :
    f 0 ^ (-(k : ℝ)⁻¹) + (q a - q 0) ≤ f a ^ (-(k : ℝ)⁻¹) := by
  let F : ℝ → ℝ := fun t ↦ f t ^ (-(k : ℝ)⁻¹) - q t
  have hFcont : ContinuousOn F (Icc 0 a) :=
    (hfcont.rpow_const (fun t ht ↦ Or.inl (hfpos t ht).ne')).sub hqcont
  have hFderiv (t : ℝ) (ht : t ∈ Ioo 0 a) :
      HasDerivAt F
        (f' t * (-(k : ℝ)⁻¹) * f t ^ (-(k : ℝ)⁻¹ - 1) - q' t) t :=
    ((hfderiv t ht).rpow_const (Or.inl (hfpos t ⟨ht.1.le, ht.2.le⟩).ne')).sub
      (hqderiv t ht)
  have hmono : MonotoneOn F (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hFcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFderiv t ht).deriv]
      have h := inverse_power_derivative_lower (f t) (f' t) (q' t) k
        (hfpos t ⟨ht.1.le, ht.2.le⟩) hk (hode t ht)
      linarith
  have hends := hmono (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.le⟩)
    (show a ∈ Icc 0 a from ⟨ha.le, le_rfl⟩) ha.le
  dsimp [F] at hends
  linarith

/-- Turning a lower bound on a negative inverse power back into an ordinary
power upper bound. -/
theorem le_inverse_pow_of_inverse_power_lower (y L : ℝ) (k : ℕ)
    (hy : 0 < y) (hL : 0 < L) (hk : 0 < k)
    (h : L ≤ y ^ (-(k : ℝ)⁻¹)) :
    y ≤ (L⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := Real.rpow_le_rpow_of_nonpos hL h (neg_nonpos.mpr hkpos.le)
  rw [← Real.rpow_mul hy.le] at hh
  have hexp : (-(k : ℝ)⁻¹) * (-(k : ℝ)) = 1 := by field_simp
  rw [hexp, Real.rpow_one, Real.rpow_neg hL.le, Real.rpow_natCast, ← inv_pow] at hh
  exact hh

/-- The nonnegative version needs no strict positivity assumption: the ODE
makes `f` nonincreasing, so either the endpoint is zero or the whole interval
has positive values and the inverse-power argument applies. -/
theorem power_decay_bound_with_clock
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfnonneg : ∀ t ∈ Icc 0 a, 0 ≤ f t)
    (hqnonneg : ∀ t ∈ Ioo 0 a, 0 ≤ q' t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹))
    (hclock : 0 < q a - q 0) :
    f a ≤ ((q a - q 0)⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hazero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have haend : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hanti : AntitoneOn f (Icc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a) hfcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hfderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hfderiv t ht).deriv]
      have hnonpos : -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkpos.le) (hqnonneg t ht))
          (Real.rpow_nonneg (hfnonneg t ⟨ht.1.le, ht.2.le⟩) _)
      exact (hode t ht).trans hnonpos
  by_cases hzero : f a = 0
  · rw [hzero]
    exact pow_nonneg (inv_nonneg.mpr hclock.le) _
  · have hfapos : 0 < f a := lt_of_le_of_ne (hfnonneg a haend) (Ne.symm hzero)
    have hfpos : ∀ t ∈ Icc 0 a, 0 < f t := by
      intro t ht
      exact hfapos.trans_le (hanti ht haend ht.2)
    have hgrowth := inverse_power_clock_growth f f' q q' a k ha hk
      hfcont hqcont hfpos hfderiv hqderiv hode
    have hlow : q a - q 0 ≤ f a ^ (-(k : ℝ)⁻¹) := by
      have hinit := Real.rpow_nonneg (hfnonneg 0 hazero) (-(k : ℝ)⁻¹)
      linarith
    exact le_inverse_pow_of_inverse_power_lower (f a) (q a - q 0) k
      hfapos hclock hk hlow

/-- The autonomous version after the time change `s = -log (1-t)`. -/
theorem power_decay_bound
    (g g' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hgcont : ContinuousOn g (Icc 0 a))
    (hgnonneg : ∀ t ∈ Icc 0 a, 0 ≤ g t)
    (hgderiv : ∀ t ∈ Ioo 0 a, HasDerivAt g (g' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      g' t ≤ -(k : ℝ) / Real.exp 1 * g t ^ (1 + (k : ℝ)⁻¹)) :
    g a ≤ (Real.exp 1 / a) ^ k := by
  have h := power_decay_bound_with_clock g g' (fun t ↦ t / Real.exp 1)
    (fun _ ↦ 1 / Real.exp 1) a k ha hk hgcont
    (continuous_id.div_const _).continuousOn hgnonneg
    (fun _ _ ↦ by positivity) hgderiv
    (fun t _ ↦ (hasDerivAt_id t).div_const (Real.exp 1))
    (fun t ht ↦ by simpa only [div_eq_mul_inv, one_mul] using hode t ht)
    (by simp only [zero_div, sub_zero]; positivity)
  simpa only [zero_div, sub_zero, inv_div] using h


end PrescribedDecay

-- Source: Theorems.Thm_RGMISFast_lemma_5_3
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma l53_condLaw_probability {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) :
    IsProbabilityMeasure (condLaw r₀ θ A rA) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure ((expMeasure (1:ℝ)).map (fun x => θ+x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold condLaw
  have : ∀ v : V, IsProbabilityMeasure
      (if r₀ v < θ then Measure.dirac (r₀ v)
       else if v ∈ A then Measure.dirac (rA v) else (expMeasure 1).map (fun x => θ+x)) := by
    intro v
    split_ifs <;> infer_instance
  infer_instance



lemma Ncount_zero_le_one {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t : ℝ) (r : V → ℝ) :
    Ncount G A 0 t r ≤ 1 := by
  classical
  unfold Ncount
  have hsub : (Finset.univ.filter (fun W : Finset V => W.card = 0 ∧
      IsAttached G A W ∧ ActiveAt G r t (A ∪ W))) ⊆ {∅} := by
    intro W hW
    exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (Finset.mem_filter.mp hW).2.1)
  simpa using Finset.card_le_card hsub

lemma Ncount_zero_integral {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t θ : ℝ)
    (r₀ rA : V → ℝ) :
    ∫⁻ r, (Ncount G A 0 t r : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤ 1 := by
  have := l53_condLaw_probability r₀ θ A rA
  calc
    _ ≤ ∫⁻ r : V → ℝ, (1:ℝ≥0∞) ∂(condLaw r₀ θ A rA) := by
      apply lintegral_mono
      intro r
      change (Ncount G A 0 t r : ℝ≥0∞) ≤ 1
      exact_mod_cast Ncount_zero_le_one G A t r
    _ = 1 := by simp

theorem RGMISFast.lemma_5_3 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (k : ℕ) :
    Measurable (fun r : V → ℝ => Ncount G A k a r) ∧
    ∫⁻ r, (Ncount G A k a r : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
      ENNReal.ofReal ((Real.exp 1 / (a - θ)) ^ k) := by
  refine ⟨Ncount_measurable_complete G A k a, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Ncount_zero_integral G A a θ r₀ rA
  · obtain ⟨f,f',hrep,hcont,hnonneg,hderiv,hode⟩ :=
      prescribed_extension_drift_complete G θ a hθ hθa r₀ hr₀ A hA hAθ rA hrA k hk
    have hb := PrescribedDecay.power_decay_bound f f' (a-θ) k (sub_pos.mpr hθa) hk
      hcont hnonneg hderiv hode
    have he := hrep (a-θ) ⟨(sub_pos.mpr hθa).le, le_rfl⟩
    rw [show θ+(a-θ) = a by ring] at he
    rw [he]
    exact ENNReal.ofReal_le_ofReal hb





-- Source: Solutions.ConditionalTailScalars
open RGMISFast
set_option autoImplicit false

lemma ct_c_gt : 1 < c := by
  unfold c
  have : 0 < 1 / (2 * Real.exp 2) := by positivity
  linarith
lemma ct_am_pos (m : ℕ) : 0 < am m := by
  unfold am a0 c
  positivity
lemma ct_oneMinus_coe (a b : ℝ) : oneMinusExp a (b : WithTop ℝ) = 1-Real.exp (-(b-a)) := by
  simp [oneMinusExp]
lemma ct_oneMinus_le (a b : ℝ) : oneMinusExp a (b : WithTop ℝ) ≤ b-a := by
  rw [ct_oneMinus_coe]
  have := Real.add_one_le_exp (-(b-a))
  linarith
lemma ct_q_growth (a : ℝ) (ha : 0 < a) :
    Real.exp 1 * oneMinusExp a ((c*a:ℝ):WithTop ℝ) / (a-a/2) ≤ Real.exp (-1) := by
  have h := ct_oneMinus_le a (c*a)
  have hle := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le) (show 0 ≤ a-a/2 by linarith)
  have he : Real.exp 1 * (c*a-a) / (a-a/2) = Real.exp (-1) := by
    unfold c
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [←Real.exp_add]; norm_num
    rw [he2,Real.exp_neg]
    field_simp
    <;> ring
  exact he ▸ hle
lemma ct_band_ratio (m i : ℕ) (hi : 1 ≤ i) (him : i < m) :
    am (i-1) / am m = c^(1+m-i) := by
  have hc : c ≠ 0 := (lt_trans (by norm_num) ct_c_gt).ne'
  have he : c^m = c^(1+m-i)*c^(i-1) := by
    rw [←pow_add]
    congr 1
    omega
  unfold am
  have ha : a0 ≠ 0 := (Real.exp_pos 2).ne'
  field_simp
  rw [he]
  <;> ring
lemma ct_band_lt (m i : ℕ) (him : i < m) : (am m : WithTop ℝ) < b i := by
  by_cases hi : i = 0
  · simp [b,hi]
  · simp only [b,if_neg hi,WithTop.coe_lt_coe]
    have hc : 0 < c := lt_trans (by norm_num) ct_c_gt
    have hp : c^(i-1) < c^m := pow_lt_pow_right₀ ct_c_gt (by omega)
    unfold am
    exact mul_lt_mul_of_pos_left (inv_strictAnti₀ (by positivity) hp) (Real.exp_pos 2)
lemma ct_q_boundary (m i : ℕ) (him : i < m) :
    Real.exp 1 * oneMinusExp (am m) (b i) / (am m-am m/2) ≤
      2*Real.exp 1*c^(1+m-i) := by
  have ha := ct_am_pos m
  have hc : 0 < c := lt_trans (by norm_num) ct_c_gt
  by_cases hi : i = 0
  · subst i
    rw [show b 0 = ⊤ by simp [b], show oneMinusExp (am m) ⊤ = 1 by simp [oneMinusExp]]
    simp only [Nat.sub_zero,mul_one]
    have hbig : 1 ≤ a0*c := le_trans (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2))
      (le_mul_of_one_le_right (Real.exp_pos 2).le ct_c_gt.le)
    have hid : am m*c^(1+m) = a0*c := by
      unfold am
      rw [pow_add]
      simp only [pow_one]
      field_simp
    apply (div_le_iff₀ (show 0 < am m-am m/2 by linarith)).mpr
    have hh := mul_le_mul_of_nonneg_left hbig (Real.exp_pos 1).le
    rw [←hid] at hh
    nlinarith [hh]
  · have hib : 1 ≤ i := by omega
    simp only [b,if_neg hi]
    have h := ct_oneMinus_le (am m) (am (i-1))
    have hle : oneMinusExp (am m) ((am (i-1):ℝ):WithTop ℝ) ≤ am (i-1) := by linarith
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle (Real.exp_pos 1).le) (show 0 ≤ am m-am m/2 by linarith)
    calc
      _ ≤ _ := hm
      _ = 2*Real.exp 1*(am (i-1)/am m) := by field_simp; ring
      _ = _ := by rw [ct_band_ratio m i hib him]

lemma ct_q_nonneg (a θ : ℝ) (hθa : θ < a) (bb : WithTop ℝ) (hab : (a:WithTop ℝ) < bb) :
    0 ≤ Real.exp 1 * oneMinusExp a bb / (a-θ) := by
  have hnon : 0 ≤ oneMinusExp a bb := by
    induction bb using WithTop.recTopCoe with
    | top => simp [oneMinusExp]
    | coe b =>
      rw [ct_oneMinus_coe]
      have hh : a < b := by exact_mod_cast hab
      have := Real.exp_le_one_iff.mpr (show -(b-a) ≤ 0 by linarith)
      linarith
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le hnon) (by linarith)

-- Source: Solutions.ConditionalExtensionBoundsComplete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
open Classical ExtensionCounts ExtensionThinning ExtensionCertificates
set_option maxHeartbeats 1000000
lemma retained_expectation_bound {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (k : ℕ)
    (bb : WithTop ℝ) (hab : (a:WithTop ℝ)<bb) :
    (∫⁻r,((retained G A k a bb r).card:ℝ≥0∞) ∂condLaw r₀ θ A rA) ≤
      ENNReal.ofReal ((Real.exp 1*oneMinusExp a bb/(a-θ))^k) := by
  have hp : 0 ≤ oneMinusExp a bb := by
    induction bb using WithTop.recTopCoe with
    | top => simp [oneMinusExp]
    | coe b =>
      rw [ct_oneMinus_coe]
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by have hh:=WithTop.coe_lt_coe.mp hab; linarith))
  rw [integral_retained G r₀ θ a hθa A rA k bb hab]
  calc
    _ ≤ ENNReal.ofReal (oneMinusExp a bb)^k * ENNReal.ofReal ((Real.exp 1/(a-θ))^k) :=
      mul_le_mul' le_rfl (RGMISFast.lemma_5_3 G θ a hθ hθa r₀ hr₀ A hA hAθ rA hrA k).2
    _ = _ := by
      rw [← ENNReal.ofReal_pow hp,← ENNReal.ofReal_mul (pow_nonneg hp k),← mul_pow]
      congr 2
      ring
 theorem conditional_extension_bounds_complete {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (bb : WithTop ℝ)
    (hab : ((a : ℝ) : WithTop ℝ) < bb) :
    (∀ k : ℕ, 1 ≤ k →
      condLaw r₀ θ A rA {r | k ≤ (GammaAB G r a bb A).card} ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      Measurable (fun r : V → ℝ => (KAB G r a bb A).choose k) ∧
      ∫⁻ r, ((KAB G r a bb A).choose k : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) := by
  have hb (k : ℕ) := retained_expectation_bound G θ a hθ hθa r₀ hr₀ A hA hAθ rA hrA k bb hab
  constructor
  · intro k hk
    have hm : Measurable (fun r : V → ℝ=>((retained G A k a bb r).card:ℝ≥0∞)) :=
      (measurable_of_countable (fun n : ℕ=>(n:ℝ≥0∞))).comp
        (card_measurable _ (fun W=>retained_mem_measurable G A W k a bb))
    calc
      _ ≤ condLaw r₀ θ A rA {r| (1:ℝ≥0∞)≤(retained G A k a bb r).card} := by
        apply measure_mono
        intro r hr
        have hh := (gamma_certificate G r a bb A k hk hr).card_pos
        change (1:ℝ≥0∞)≤(retained G A k a bb r).card
        exact_mod_cast hh
      _ ≤ ∫⁻r,((retained G A k a bb r).card:ℝ≥0∞) ∂condLaw r₀ θ A rA := by
        simpa using meas_ge_le_lintegral_div hm.aemeasurable (by norm_num : (1:ℝ≥0∞)≠0) (by norm_num : (1:ℝ≥0∞)≠⊤)
      _ ≤ _ := hb k
  · intro k hk
    refine ⟨(measurable_of_countable (fun n : ℕ=>n.choose k)).comp (boundary_measurable G A a bb),?_⟩
    apply le_trans (lintegral_mono (fun r=>?_)) (hb k)
    change ((KAB G r a bb A).choose k : ℝ≥0∞) ≤ ((retained G A k a bb r).card : ℝ≥0∞)
    exact_mod_cast boundary_choose_le G r a bb A k hk

-- Source: Solutions.BinomialMomentTailComplete
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BinomialMomentTail
lemma choose_lower (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n:ℝ)/(k:ℝ))^k ≤ (n.choose k : ℝ) := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hzero : k = 0
      · subst k; simp
      have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk1 : (0:ℝ) < k+1 := by positivity
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
      have hratio : ((n:ℝ)+1)/((k:ℝ)+1) ≤ (n:ℝ)/(k:ℝ) := by
        apply (div_le_div_iff₀ hk1 hkpos).mpr
        have hh : (k:ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
        nlinarith
      have hh := ih n (by omega) (by omega)
      have hp := (pow_le_pow_left₀ (by positivity : 0 ≤ ((n:ℝ)+1)/((k:ℝ)+1)) hratio k).trans hh
      have he : ((n:ℝ)+1)*(n.choose k:ℝ) = ((n+1).choose (k+1):ℝ)*((k:ℝ)+1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n k
      simp only [Nat.cast_add,Nat.cast_one,pow_succ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hk1).mpr
      rw [← he]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (n:ℝ)+1)
end BinomialMomentTail
open BinomialMomentTail
 theorem binomial_moment_exponential_tail_complete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Measurable (fun ω => (K ω).choose k) ∧
      ∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k))
    (x : ℝ) (hx : 1 ≤ x) :
    μ {ω | 32*C*x < (K ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  let k := ⌊x⌋₊+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hxk : x < (k:ℝ) := by simpa [k] using Nat.lt_floor_add_one x
  have hkx : (k:ℝ) ≤ 2*x := by
    have hh := Nat.floor_le (show 0 ≤ x by linarith)
    dsimp [k]; push_cast; linarith
  have hCp : 0 < C := by linarith
  have hsub : {ω | 32*C*x < (K ω:ℝ)} ⊆
      {ω | ENNReal.ofReal ((16*C)^k) ≤ ((K ω).choose k : ℝ≥0∞)} := by
    intro ω hω
    change 32*C*x < (K ω:ℝ) at hω
    have hscale : 16*C*(k:ℝ) < (K ω:ℝ) := by nlinarith
    have hkn : k ≤ K ω := by
      have : (k:ℝ) ≤ K ω := by nlinarith
      exact_mod_cast this
    have hh := choose_lower (K ω) k hk hkn
    have hratio : 16*C ≤ (K ω:ℝ)/(k:ℝ) := (le_div_iff₀ hkpos).mpr hscale.le
    have hb := (pow_le_pow_left₀ (by positivity : 0 ≤ 16*C) hratio k).trans hh
    simpa using ENNReal.ofReal_le_ofReal hb
  have hm : Measurable (fun ω => ((K ω).choose k : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (hmom k hk).1
  have he : Real.exp 1/8 ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have h := Real.exp_one_lt_d9
    have hp := Real.exp_pos 1
    rw [← one_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  calc
    _ ≤ μ {ω | ENNReal.ofReal ((16*C)^k) ≤ ((K ω).choose k : ℝ≥0∞)} := measure_mono hsub
    _ ≤ (∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ) / ENNReal.ofReal ((16*C)^k) :=
      meas_ge_le_lintegral_div hm.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k) / ENNReal.ofReal ((16*C)^k) :=
      ENNReal.div_le_div_right (hmom k hk).2 _
    _ = ENNReal.ofReal ((Real.exp 1/8)^k) := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity), ← div_pow]
      congr 2
      field_simp
      <;> ring
    _ ≤ ENNReal.ofReal ((Real.exp (-1))^k) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) he k)
    _ = ENNReal.ofReal (Real.exp (-(k:ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

-- Source: Solutions.ConditionalGrowthTail
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma ct_discrete_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (q : ℝ) (hq : 0 ≤ q) (hqexp : q ≤ Real.exp (-1))
    (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ N ω} ≤ ENNReal.ofReal (q^k))
    (x : ℝ) (hx : 0 ≤ x) : μ {ω | x < (N ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  let k := ⌊x⌋₊+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hxk : x < (k:ℝ) := by simpa [k] using Nat.lt_floor_add_one x
  have hsub : {ω | x < (N ω:ℝ)} ⊆ {ω | k ≤ N ω} := by
    intro ω hω
    have hh : (⌊x⌋₊:ℝ) < (N ω:ℝ) := lt_of_le_of_lt (Nat.floor_le hx) hω
    have hn : ⌊x⌋₊ < N ω := by exact_mod_cast hh
    dsimp [k]
    omega
  calc
    _ ≤ μ {ω | k ≤ N ω} := measure_mono hsub
    _ ≤ _ := htail k hk
    _ ≤ ENNReal.ofReal ((Real.exp (-1))^k) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hq hqexp _)
    _ = ENNReal.ofReal (Real.exp (-(k:ℝ))) := by
      rw [←Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

-- Source: Theorems.Thm_RGMISFast_lemma_6_1
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

theorem RGMISFast.lemma_6_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (bb : WithTop ℝ)
    (hab : ((a : ℝ) : WithTop ℝ) < bb) :
    (∀ k : ℕ, 1 ≤ k →
      condLaw r₀ θ A rA {r | k ≤ (GammaAB G r a bb A).card} ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      Measurable (fun r : V → ℝ => (KAB G r a bb A).choose k) ∧
      ∫⁻ r, ((KAB G r a bb A).choose k : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (θ = a / 2 → ∀ x : ℝ, 0 ≤ x →
      condLaw r₀ θ A rA {r | x < ((GammaAB G r a ((c * a : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-x))) ∧
    (∀ m i : ℕ, i < m → θ = a / 2 → a = am m → ∀ x : ℝ, 1 ≤ x →
      condLaw r₀ θ A rA {r | 32 * c ^ (1 + m - i) * x < (Kmi G r m i A : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-x))) := by
  have hbase := conditional_extension_bounds_complete G θ a hθ hθa r₀ hr₀ A hA hAθ rA hrA bb hab
  refine ⟨hbase.1,hbase.2,?_,?_⟩
  · intro he x hx
    subst θ
    have ha : 0 < a := by linarith
    have hab' : (a:WithTop ℝ) < ((c*a:ℝ):WithTop ℝ) := by
      apply WithTop.coe_lt_coe.mpr
      nlinarith [ct_c_gt]
    exact ct_discrete_tail (condLaw r₀ (a/2) A rA)
      (fun r => (GammaAB G r a ((c*a:ℝ):WithTop ℝ) A).card)
      _ (ct_q_nonneg a (a/2) hθa _ hab') (ct_q_growth a ha)
      (conditional_extension_bounds_complete G (a/2) a hθ hθa r₀ hr₀ A hA hAθ rA hrA _ hab').1 x hx
  · intro m i hi he hea x hx
    subst θ
    subst a
    have hc : 1 ≤ c^(1+m-i) := one_le_pow₀ ct_c_gt.le
    have hmom := (conditional_extension_bounds_complete G (am m/2) (am m) hθ hθa
      r₀ hr₀ A hA hAθ rA hrA (b i) (ct_band_lt m i hi)).2
    apply binomial_moment_exponential_tail_complete (condLaw r₀ (am m/2) A rA)
      (fun r => Kmi G r m i A) (c^(1+m-i)) hc ?_ x hx
    intro k hk
    refine ⟨(hmom k hk).1, (hmom k hk).2.trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (ct_q_nonneg (am m) (am m/2) hθa (b i) (ct_band_lt m i hi))
      (ct_q_boundary m i hi) k)





-- Source: Solutions.ConditionalBadEventWeightedComplete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
open Classical ConditionalWeightedTail ConditionalHistorySupport BadEventMeasurability
set_option maxHeartbeats 1000000
 theorem conditional_bad_event_weighted_bound_complete {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (L : ℝ) (hL : 8 ≤ L) (m : ℕ) (hm : 1 ≤ m) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ (am m / 2)) (A : Finset V) (hA : IsRootConnected G u A) :
    condLaw r₀ (am m / 2) ∅ (fun _ => 0)
      {r | 2 * S r A (am m) + L < ((GammaAB G r (am m) ((c * am m : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
        (if ActiveAt G r₀ (am m / 2) A then 1 else 0) * (∫⁻ r in {r | ∀ v ∈ A, am m ≤ r v},
          ENNReal.ofReal (Real.exp (-(2 * S r A (am m) + L))) ∂(condLaw r₀ (am m / 2) ∅ (fun _ => 0))) ∧
    ∀ i : ℕ, i < m →
      condLaw r₀ (am m / 2) ∅ (fun _ => 0)
        {r | 32 * c ^ (1 + m - i) * (2 * S r A (am m) + L) < (Kmi G r m i A : ℝ)} ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) * (∫⁻ r in {r | ∀ v ∈ A, am m ≤ r v},
          ENNReal.ofReal (Real.exp (-(2 * S r A (am m) + L))) ∂(condLaw r₀ (am m / 2) ∅ (fun _ => 0))) := by
  have ha := ct_am_pos m
  have hθ : 0 ≤ am m/2 := by positivity
  have hθa : am m/2<am m := by linarith
  have hconn : IsConnectedSet G A := ⟨⟨u,hA.1⟩,fun x hx y hy=>(hA.2 x hx).symm.trans (hA.2 y hy)⟩
  have hab : (am m:WithTop ℝ)<((c*am m:ℝ):WithTop ℝ) := by
    apply WithTop.coe_lt_coe.mpr
    nlinarith [ct_c_gt]
  have hthreshold (rA : V→ℝ) (hrA : ∀v∈A,am m ≤ rA v) : 1 ≤ 2*S rA A (am m)+L := by
    have hs := S_nonneg rA A (am m) ha.le (fun v hv=>ha.le.trans (hrA v hv))
    linarith
  constructor
  · have hh := weighted_bound G r₀ (am m/2) (am m) L 1 hθ hθa (by linarith) (by norm_num) hr₀ A
      (fun r=>(GammaAB G r (am m) ((c*am m:ℝ):WithTop ℝ) A).card)
      (gamma_measurable G A _ _) (fun r hp=>by
        by_contra hn
        simp [GammaAB,hn] at hp) (fun hact rA hrA=>by
          have hh := (RGMISFast.lemma_6_1 G (am m/2) (am m) hθ hθa r₀ hr₀ A hconn hact rA hrA _ hab).2.2.1 rfl
            (2*S rA A (am m)+L) (by linarith [hthreshold rA hrA])
          simpa only [one_mul] using hh)
    simpa only [one_mul] using hh
  · intro i hi
    apply weighted_bound G r₀ (am m/2) (am m) L (32*c^(1+m-i)) hθ hθa (by linarith)
      (by have hc:=ct_c_gt; positivity) hr₀ A (fun r=>Kmi G r m i A)
      (ExtensionThinning.boundary_measurable G A _ _) (fun r hp=>by
        by_contra hn
        simp [Kmi,KAB,hn] at hp)
    intro hact rA hrA
    exact (RGMISFast.lemma_6_1 G (am m/2) (am m) hθ hθa r₀ hr₀ A hconn hact rA hrA _ hab).2.2.2
      m i hi rfl rfl (2*S rA A (am m)+L) (hthreshold rA hrA)

-- Source: Solutions.Eq29Complete

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

lemma condLaw_probability {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) :
    IsProbabilityMeasure (condLaw r₀ θ A rA) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure ((expMeasure (1:ℝ)).map (fun x => θ+x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold condLaw
  have : ∀ v : V, IsProbabilityMeasure
      (if r₀ v < θ then Measure.dirac (r₀ v)
       else if v ∈ A then Measure.dirac (rA v) else (expMeasure 1).map (fun x => θ+x)) := by
    intro v
    split_ifs <;> infer_instance
  infer_instance

lemma eq29_am_positive (m : ℕ) : 0 < am m := by
  unfold am a0 c
  positivity

theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (L : ℝ) (hL : 8 ≤ L) (m : ℕ) (hm : 1 ≤ m) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ (am m / 2)) (A : Finset V) (hA : IsRootConnected G u A) :
    (condLaw r₀ (am m / 2) ∅ (fun _ => 0)
        {r | 2 * S r A (am m) + L < ((GammaAB G r (am m) ((c * am m : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ∧
      (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card)) ∧
    ∀ i : ℕ, i < m →
      condLaw r₀ (am m / 2) ∅ (fun _ => 0)
          {r | 32 * c ^ (1 + m - i) * (2 * S r A (am m) + L) < (Kmi G r m i A : ℝ)} ≤
            (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
                ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ∧
        (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
                ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
            (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) := by
  have hpos := eq29_am_positive m
  have hweighted := conditional_bad_event_weighted_bound_complete G u L hL m hm r₀ hr₀ A hA
  have hlap := conditional_rank_charge_laplace_complete r₀ (am m / 2) (am m) L hpos (by linarith) A
  rw [hlap] at hweighted
  haveI := condLaw_probability r₀ (am m / 2) ∅ (fun _ => 0)
  have hprob : condLaw r₀ (am m / 2) ∅ (fun _ => 0)
      {r | ∀ v ∈ A, am m ≤ r v} ≤ 1 := prob_le_one
  have hdrop :
      (if ActiveAt G r₀ (am m / 2) A then (1:ℝ≥0∞) else 0) *
        condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
          ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
      (if ActiveAt G r₀ (am m / 2) A then (1:ℝ≥0∞) else 0) *
          ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) := by
    calc
      _ ≤ (if ActiveAt G r₀ (am m / 2) A then (1:ℝ≥0∞) else 0) * 1 *
            ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) :=
        mul_le_mul_left (mul_le_mul_right hprob _) _
      _ = _ := by rw [mul_one]
  exact ⟨⟨by simpa only [mul_assoc] using hweighted.1, hdrop⟩,
    fun i hi => ⟨by simpa only [mul_assoc] using hweighted.2 i hi, hdrop⟩⟩



#print axioms solution
