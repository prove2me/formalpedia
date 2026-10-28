-- Prove2me | solution 1 for ValuePersPricing.Deviation.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:31:43.317177+00:00
-- url     : https://prove2.me/submissions/2ede3235-7b33-46eb-99f1-d38887832674

import Definitions.Def_ValuePersPricing_Deviation_Model
import Init
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem tail_nonneg (ν : Measure ℝ) (p : ℝ) : 0 ≤ tail ν p := ENNReal.toReal_nonneg

theorem price_profit_le_surplus (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (p : ℝ) :
    (p-c)*tail ν p ≤ mean ν-c := by
  letI := hm.isProb
  have hf : Integrable ((Ici p).indicator (fun _ : ℝ=>p-c)) ν :=
    (integrable_const (p-c)).indicator measurableSet_Ici
  have hg : Integrable (fun v : ℝ=>v-c) ν := hm.integrable.sub (integrable_const c)
  have he : ∀ᵐ v ∂ν,(Ici p).indicator (fun _ : ℝ=>p-c) v ≤ v-c := by
    filter_upwards [hm.ge_cost] with v hv
    by_cases hp : v∈Ici p
    · simp only [Set.indicator_of_mem hp]
      exact sub_le_sub_right hp c
    · simp only [Set.indicator_of_notMem hp]
      linarith
  have hi:=integral_mono_ae hf hg he
  rw [integral_indicator measurableSet_Ici,integral_const,integral_sub hm.integrable (integrable_const c),integral_const] at hi
  simpa [mean,tail,measureReal_def,smul_eq_mul,mul_comm] using hi

theorem price_range_bounded (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) :
    BddAbove (range fun p : ℝ=>(p-c)*tail ν p) := by
  refine ⟨mean ν-c,?_⟩
  rintro _ ⟨p,rfl⟩
  exact price_profit_le_surplus ν c hm p

theorem price_le_sp (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (p : ℝ) :
    (p-c)*tail ν p ≤ spProfit ν c :=
  le_csSup (price_range_bounded ν c hm) (mem_range_self p)

theorem sp_nonneg (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) : 0 ≤ spProfit ν c := by
  simpa using price_le_sp ν c hm c

theorem sp_le_surplus (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) : spProfit ν c ≤ mean ν-c := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨p,rfl⟩
  exact price_profit_le_surplus ν c hm p

theorem mean_ge_cost (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) : c ≤ mean ν := by
  have h:=(sp_nonneg ν c hm).trans (sp_le_surplus ν c hm)
  linarith

theorem pricing_inequality (ν : Measure ℝ) (hm : Market ν 0) (x : ℝ) (hx : 0 < x) :
    tail ν x ≤ spProfit ν 0/x := by
  apply (le_div_iff₀ hx).mpr
  simpa only [sub_zero,mul_comm] using price_le_sp ν 0 hm x
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set Filter Topology
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

def lambertKernel (w : ℝ) : ℝ := w*Real.exp w

theorem kernel_continuous : Continuous lambertKernel := continuous_id.mul Real.continuous_exp

theorem kernel_hasDeriv (w : ℝ) : HasDerivAt lambertKernel (Real.exp w*(1+w)) w := by
  change HasDerivAt (fun x : ℝ => x*Real.exp x) _ w
  have h : HasDerivAt (fun x : ℝ => x*Real.exp x) (1*Real.exp w+w*Real.exp w) w :=
    (hasDerivAt_id w).mul (Real.hasDerivAt_exp w)
  convert h using 1 <;> ring

theorem kernel_strictAnti : StrictAntiOn lambertKernel (Iic (-1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _) kernel_continuous.continuousOn
  intro w hw
  have hw' : w < -1 := by simpa using hw
  rw [(kernel_hasDeriv w).deriv]
  exact mul_neg_of_pos_of_neg (Real.exp_pos w) (by linarith)

theorem kernel_strictMono : StrictMonoOn lambertKernel (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) kernel_continuous.continuousOn
  intro w hw
  have hw' : -1 < w := by simpa using hw
  rw [(kernel_hasDeriv w).deriv]
  exact mul_pos (Real.exp_pos w) (by linarith)

theorem kernel_boundary : lambertKernel (-1) = -1 / Real.exp 1 := by
  simp [lambertKernel,Real.exp_neg,div_eq_mul_inv]

theorem kernel_limit : Tendsto lambertKernel atBot (𝓝 0) := by
  have h:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_neg_atBot_atTop
  change Tendsto (fun w : ℝ => w*Real.exp w) atBot (𝓝 0)
  simpa using h.neg

theorem lower_root_exists (x : ℝ) (hx : -1/Real.exp 1 ≤ x) (hx0 : x<0) :
    ∃ w : ℝ,w≤-1 ∧ lambertKernel w=x := by
  have he : ∀ᶠ w in atBot,x<lambertKernel w := kernel_limit.eventually (eventually_gt_nhds hx0)
  obtain ⟨a,ha,ha1⟩:=(he.and (eventually_le_atBot (-1))).exists
  obtain ⟨w,hw,heq⟩:=intermediate_value_Icc' ha1 kernel_continuous.continuousOn
    (show x ∈ Icc (lambertKernel (-1)) (lambertKernel a) by rw [kernel_boundary];exact ⟨hx,ha.le⟩)
  exact ⟨w,hw.2,heq⟩

theorem upper_root_exists (x : ℝ) (hx : -1/Real.exp 1 ≤ x) (hx0 : x≤0) :
    ∃ w : ℝ,-1≤w ∧ lambertKernel w=x := by
  obtain ⟨w,hw,heq⟩:=intermediate_value_Icc (show (-1:ℝ)≤0 by norm_num) kernel_continuous.continuousOn
    (show x ∈ Icc (lambertKernel (-1)) (lambertKernel 0) by rw [kernel_boundary];simpa [lambertKernel] using And.intro hx hx0)
  exact ⟨w,hw.1,heq⟩

theorem kernel_minimum (w : ℝ) : -1/Real.exp 1 ≤ lambertKernel w := by
  rw [←kernel_boundary]
  rcases le_total w (-1) with h|h
  · exact kernel_strictAnti.antitoneOn h (by simp) h
  · exact kernel_strictMono.monotoneOn (by simp) h h

theorem boundary_unique (w : ℝ) (hw : lambertKernel w = -1/Real.exp 1) : w = -1 := by
  have heq : lambertKernel w=lambertKernel (-1) := hw.trans kernel_boundary.symm
  rcases le_total w (-1) with h|h
  · exact kernel_strictAnti.injOn h (by simp) heq
  · exact kernel_strictMono.injOn h (by simp) heq

theorem kernel_two_roots (x : ℝ) (hx : -1/Real.exp 1 < x) (hx0 : x<0) :
    {w : ℝ | w*Real.exp w=x}.ncard=2 := by
  classical
  obtain ⟨a,ha,hea⟩:=lower_root_exists x hx.le hx0
  obtain ⟨b,hb,heb⟩:=upper_root_exists x hx.le hx0.le
  have hab : a ≠ b := by
    intro h
    have he : a = -1 := le_antisymm ha (h ▸ hb)
    rw [he,kernel_boundary] at hea
    linarith
  have hs : {w : ℝ | w*Real.exp w=x}= {a,b} := by
    ext w
    change lambertKernel w=x ↔ w ∈ ({a,b}:Set ℝ)
    simp only [mem_insert_iff,mem_singleton_iff]
    constructor
    · intro hw
      rcases le_total w (-1) with h|h
      · exact Or.inl (kernel_strictAnti.injOn h ha (hw.trans hea.symm))
      · exact Or.inr (kernel_strictMono.injOn h hb (hw.trans heb.symm))
    · rintro (rfl|rfl) <;> assumption
  rw [hs]
  simp [hab]
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem pareto_tail_ge (a p : ℝ) (ha : 0<a) (hp : a≤p) :
    tail (paretoMeasure a 1) p=a/p := by
  have hp0 : 0<p:=ha.trans_le hp
  have heq : (∫⁻v in Ici p,paretoPDF a 1 v)=
      ∫⁻v in Ici p,ENNReal.ofReal (a*v^(-2:ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ici
    intro v hv
    have hav : a≤v:=hp.trans hv
    norm_num [paretoPDF,paretoPDFReal,hav,Real.rpow_neg,Real.rpow_natCast]
  unfold tail paretoMeasure
  rw [withDensity_apply _ measurableSet_Ici,heq]
  rw [←integral_eq_lintegral_of_nonneg_ae]
  · rw [integral_const_mul,integral_Ici_eq_integral_Ioi,
      integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hp0]
    norm_num [Real.rpow_neg_one,div_eq_mul_inv]
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    have hv0 : 0<v:=hp0.trans_le hv
    positivity
  · fun_prop

theorem pareto_ge_minimum (a : ℝ) (ha : 0<a) : ∀ᵐv ∂paretoMeasure a 1,a≤v := by
  have hz : paretoMeasure a 1 (Iio a)=0 := by
    rw [paretoMeasure,withDensity_apply _ measurableSet_Iio]
    exact lintegral_paretoPDF_of_le le_rfl
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with v hv
  exact le_of_not_gt hv

theorem pareto_tail_le (a p : ℝ) (ha : 0<a) (hp : p≤a) :
    tail (paretoMeasure a 1) p=1 := by
  letI:=isProbabilityMeasure_paretoMeasure ha (by norm_num : (0:ℝ)<1)
  have h : ∀ᵐv ∂paretoMeasure a 1,v∈Ici p := (pareto_ge_minimum a ha).mono (fun _ hv=>hp.trans hv)
  have hm : paretoMeasure a 1 (Ici p)=1 := by
    exact (measure_congr (eventuallyEq_univ.mpr h)).trans (by simp)
  simp [tail,hm]

def cappedPareto (a B : ℝ) : Measure ℝ := (paretoMeasure a 1).map (fun v=>min B v)

theorem capped_pareto_probability (a B : ℝ) (ha : 0<a) : IsProbabilityMeasure (cappedPareto a B) := by
  letI:=isProbabilityMeasure_paretoMeasure ha (by norm_num : (0:ℝ)<1)
  unfold cappedPareto
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem capped_pareto_tail (a B p : ℝ) (ha : 0<a) :
    tail (cappedPareto a B) p=if p≤B then (if p≤a then 1 else a/p) else 0 := by
  unfold tail cappedPareto
  rw [Measure.map_apply (by fun_prop) measurableSet_Ici]
  by_cases hpB:p≤B
  · have he : (fun v:ℝ=>min B v) ⁻¹' Ici p=Ici p := by ext v;simp [hpB,le_min_iff]
    rw [he,if_pos hpB]
    by_cases hpa:p≤a
    · rw [if_pos hpa];exact pareto_tail_le a p ha hpa
    · rw [if_neg hpa];exact pareto_tail_ge a p ha (le_of_not_ge hpa)
  · have he : (fun v:ℝ=>min B v) ⁻¹' Ici p=∅ := by ext v;simp [hpB,le_min_iff]
    simp [he,hpB]

theorem capped_pareto_bounds (a B : ℝ) (ha : 0<a) (haB : a≤B) :
    ∀ᵐv ∂cappedPareto a B,a≤v ∧ v≤B := by
  rw [cappedPareto,ae_map_iff (by fun_prop) measurableSet_Icc]
  filter_upwards [pareto_ge_minimum a ha] with v hv
  exact ⟨le_min haB hv,min_le_left _ _⟩

theorem capped_pareto_market (a B : ℝ) (ha : 0<a) (haB : a≤B) : Market (cappedPareto a B) 0 := by
  letI:=capped_pareto_probability a B ha
  have hb:=capped_pareto_bounds a B ha haB
  refine ⟨inferInstance,le_rfl,hb.mono (fun v h=>ha.le.trans h.1),?_⟩
  apply (integrable_const B).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hb] with v hv
  simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (ha.le.trans hv.1)] using hv.2
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem standardizing_measurable (ν : Measure ℝ) (c : ℝ) :
    Measurable (fun v : ℝ=>(v-c)/(mean ν-c)) :=
  (measurable_id.sub_const c).div_const _

theorem standardized_market (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    Market (standardize ν c) 0 := by
  letI := hm.isProb
  have hs : 0 < mean ν-c := sub_pos.mpr hc
  have hf := standardizing_measurable ν c
  refine ⟨Measure.isProbabilityMeasure_map hf.aemeasurable,le_rfl,?_,?_⟩
  · apply (ae_map_iff hf.aemeasurable measurableSet_Ici).mpr
    filter_upwards [hm.ge_cost] with v hv
    exact div_nonneg (sub_nonneg.mpr hv) hs.le
  · apply (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr
    exact (hm.integrable.sub (integrable_const c)).div_const (mean ν-c)

theorem standardized_mean (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    mean (standardize ν c)=1 := by
  letI := hm.isProb
  unfold mean standardize
  rw [integral_map (μ:=ν) (f:=fun v : ℝ=>v) (standardizing_measurable ν c).aemeasurable measurable_id.aestronglyMeasurable]
  rw [integral_div,integral_sub hm.integrable (integrable_const c)]
  simp only [integral_const]
  simpa [mean,measureReal_def] using div_self (sub_pos.mpr hc).ne'

theorem standardized_Ici (ν : Measure ℝ) (c q : ℝ) (hc : c < mean ν) :
    standardize ν c (Ici q)=ν (Ici (c+(mean ν-c)*q)) := by
  rw [standardize,Measure.map_apply (standardizing_measurable ν c) measurableSet_Ici]
  congr 1
  ext v
  simp only [mem_preimage,mem_Ici]
  rw [le_div_iff₀ (sub_pos.mpr hc)]
  constructor  <;> intro h  <;> nlinarith

theorem standardized_Ioi (ν : Measure ℝ) (c q : ℝ) (hc : c < mean ν) :
    standardize ν c (Ioi q)=ν (Ioi (c+(mean ν-c)*q)) := by
  rw [standardize,Measure.map_apply (standardizing_measurable ν c) measurableSet_Ioi]
  congr 1
  ext v
  simp only [mem_preimage,mem_Ioi]
  rw [lt_div_iff₀ (sub_pos.mpr hc)]
  constructor  <;> intro h  <;> nlinarith

theorem standardized_tail (ν : Measure ℝ) (c p : ℝ) (hc : c < mean ν) :
    tail (standardize ν c) ((p-c)/(mean ν-c))=tail ν p := by
  unfold tail
  rw [standardized_Ici ν c _ hc]
  have he : c+(mean ν-c)*((p-c)/(mean ν-c))=p := by
    field_simp [(sub_pos.mpr hc).ne']
     <;> ring
  rw [he]
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

theorem atom_at_price_is_included (v : ℝ) : tail (Measure.dirac v) v=1 ∧ Measure.dirac v (Ioi v)=0 := by
  simp [tail,Measure.dirac_apply',measurableSet_Ici,measurableSet_Ioi]

theorem deterministic_market (v c : ℝ) (hc : 0 ≤ c) (hv : c ≤ v) : Market (Measure.dirac v) c := by
  refine ⟨inferInstance,hc,?_,?_⟩
  · simpa using hv
  · exact integrable_dirac (by simp)

theorem deterministic_profit (v c : ℝ) (hc : 0 ≤ c) (hv : c ≤ v) :
    spProfit (Measure.dirac v) c=v-c := by
  have hm:=deterministic_market v c hc hv
  apply le_antisymm
  · simpa [mean] using sp_le_surplus (Measure.dirac v) c hm
  · simpa [(atom_at_price_is_included v).1] using price_le_sp (Measure.dirac v) c hm v
end Queelius.PersonalizedPricing.Controls

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem centered_integral_zero (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) :
    (∫ v, v-mean ν ∂ν)=0 := by
  letI:=hm.isProb
  rw [integral_sub hm.integrable (integrable_const _),integral_const]
  simp [mean]

theorem deviation_upper_part (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) :
    coefDev ν = (∫ v,max (v-mean ν) 0 ∂ν)/mean ν := by
  letI:=hm.isProb
  have h:=integral_abs_eq_two_mul_integral_posPart_sub_integral
    (hm.integrable.sub (integrable_const (mean ν)))
  simp only [Pi.sub_apply] at h
  rw [centered_integral_zero ν c hm,sub_zero] at h
  rw [coefDev,h]
  simp only [PosPart.posPart]
  ring

theorem deviation_lower_part (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) :
    coefDev ν = (∫ v,max (mean ν-v) 0 ∂ν)/mean ν := by
  letI:=hm.isProb
  have h:=integral_abs_eq_two_mul_integral_negPart_add_integral
    (hm.integrable.sub (integrable_const (mean ν)))
  simp only [Pi.sub_apply] at h
  rw [centered_integral_zero ν c hm,add_zero] at h
  rw [coefDev,h]
  simp only [NegPart.negPart,neg_sub]
  ring

theorem scale_ae_bound (ν : Measure ℝ) (S : ℝ) (hS : IsScale ν S) :
    ∀ᵐ v ∂ν,v≤S*mean ν := by
  have h:=measure_eq_zero_iff_ae_notMem.mp hS.1
  filter_upwards [h] with v hv
  exact le_of_not_gt hv

theorem scale_mean_bound (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c) (hS : IsScale ν S) :
    mean ν ≤ S*mean ν := by
  letI:=hm.isProb
  have h:=integral_mono_ae hm.integrable (integrable_const (S*mean ν)) (scale_ae_bound ν S hS)
  simpa [mean] using h

theorem lower_tail_complement (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν.real (Iio x)=1-tail ν x := by
  rw [←compl_Ici,measureReal_compl measurableSet_Ici]
  simp [tail,measureReal_def]
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set Filter Topology
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem lambert_spec (x : ℝ) (hx : -1/Real.exp 1 ≤ x) (hx0 : x<0) :
    lambertWm1 x≤-1 ∧ lambertWm1 x*Real.exp (lambertWm1 x)=x ∧
    ∀ w : ℝ,w≤-1 → w*Real.exp w=x → w=lambertWm1 x := by
  classical
  have he : ∃ w : ℝ,w≤-1 ∧ w*Real.exp w=x := lower_root_exists x hx hx0
  have hs:=Classical.choose_spec he
  have hv : lambertWm1 x=Classical.choose he := by simp only [lambertWm1,dif_pos he]
  rw [hv]
  refine ⟨hs.1,hs.2,?_⟩
  intro w hw hwe
  exact kernel_strictAnti.injOn hw hs.1 (hwe.trans hs.2.symm)

theorem lambert_boundary : lambertWm1 (-1/Real.exp 1) = -1 := by
  have hneg : -1/Real.exp 1 < 0 := div_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)
  exact boundary_unique _ (lambert_spec _ le_rfl hneg).2.1

theorem lambert_antitone : AntitoneOn lambertWm1 (Ico (-1/Real.exp 1) 0) := by
  intro x hx y hy hxy
  have hxs:=lambert_spec x hx.1 hx.2
  have hys:=lambert_spec y hy.1 hy.2
  by_contra h
  have hlt:=kernel_strictAnti hxs.1 hys.1 (lt_of_not_ge h)
  change lambertWm1 y*Real.exp (lambertWm1 y)<lambertWm1 x*Real.exp (lambertWm1 x) at hlt
  rw [hxs.2.1,hys.2.1] at hlt
  exact (not_lt_of_ge hxy) hlt

theorem lambert_limit : Tendsto lambertWm1 (𝓝[<] 0) atBot := by
  apply tendsto_atBot.2
  intro B
  let a : ℝ := min B (-1)
  have ha1 : a≤-1 := min_le_right _ _
  have haB : a≤B := min_le_left _ _
  have haneg : lambertKernel a<0 := mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos a)
  have he : ∀ᶠ x : ℝ in 𝓝[<] 0,lambertKernel a<x :=
    (eventually_gt_nhds haneg).filter_mono nhdsWithin_le_nhds
  have hn : ∀ᶠ x : ℝ in 𝓝[<] 0,x<0 := self_mem_nhdsWithin
  filter_upwards [he,hn] with x hx hx0
  have hxs:=lambert_spec x ((kernel_minimum a).trans hx.le) hx0
  have hwa : lambertWm1 x≤a := by
    by_contra h
    have hlt:=kernel_strictAnti ha1 hxs.1 (lt_of_not_ge h)
    change lambertWm1 x*Real.exp (lambertWm1 x)<lambertKernel a at hlt
    rw [hxs.2.1] at hlt
    exact (not_lt_of_ge hx.le) hlt
  exact hwa.trans haB

theorem lambert_all_facts :
    (∀ x ∈ Ioo (-1/Real.exp 1) 0,{w : ℝ | w*Real.exp w=x}.ncard=2) ∧
    {w : ℝ | w*Real.exp w= -1/Real.exp 1}={-1} ∧
    (∀ x : ℝ,-1/Real.exp 1 ≤ x → x<0 →
      lambertWm1 x≤-1 ∧ lambertWm1 x*Real.exp (lambertWm1 x)=x ∧
      ∀ w : ℝ,w≤-1 → w*Real.exp w=x → w=lambertWm1 x) ∧
    lambertWm1 (-1/Real.exp 1)= -1 ∧
    Tendsto lambertWm1 (𝓝[<] 0) atBot ∧
    AntitoneOn lambertWm1 (Ico (-1/Real.exp 1) 0) := by
  refine ⟨fun x hx=>kernel_two_roots x hx.1 hx.2,?_,lambert_spec,lambert_boundary,lambert_limit,lambert_antitone⟩
  ext w
  simp only [mem_setOf_eq,mem_singleton_iff]
  constructor
  · exact boundary_unique w
  · rintro rfl
    exact kernel_boundary
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

def paretoMixture (q a B : ℝ) : Measure ℝ :=
  ENNReal.ofReal q • cappedPareto a B + ENNReal.ofReal (1-q) • Measure.dirac 0

theorem pareto_mixture_probability (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a) :
    IsProbabilityMeasure (paretoMixture q a B) := by
  letI:=capped_pareto_probability a B ha
  constructor
  simp only [paretoMixture,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add hq0 (by linarith)]
  norm_num

theorem pareto_mixture_tail (q a B p : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a) :
    tail (paretoMixture q a B) p=q*tail (cappedPareto a B) p+
      (1-q)*(if p≤0 then 1 else 0) := by
  letI:=capped_pareto_probability a B ha
  unfold tail paretoMixture
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hq0,
    ENNReal.toReal_ofReal (show 0≤1-q by linarith)]
  by_cases hp:p≤0 <;> simp [Measure.dirac_apply',hp]

theorem pareto_mixture_bounds (q a B : ℝ) (ha : 0<a) (haB : a≤B) :
    ∀ᵐv ∂paretoMixture q a B,0≤v ∧ v≤B := by
  have hb : 0≤B:=ha.le.trans haB
  unfold paretoMixture
  apply ae_add_measure_iff.mpr
  constructor
  · apply Measure.ae_smul_measure
    exact (capped_pareto_bounds a B ha haB).mono (fun v h=>⟨ha.le.trans h.1,h.2⟩)
  · apply Measure.ae_smul_measure
    simp [hb]

theorem pareto_mixture_market (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a) (haB : a≤B) :
    Market (paretoMixture q a B) 0 := by
  letI:=pareto_mixture_probability q a B hq0 hq1 ha
  have hb:=pareto_mixture_bounds q a B ha haB
  refine ⟨inferInstance,le_rfl,hb.mono (fun _ h=>h.1),?_⟩
  apply (integrable_const B).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hb] with v hv
  simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg hv.1] using hv.2

theorem pareto_mixture_endpoint_atom (q a B : ℝ) (hq0 : 0<q) (hq1 : q≤1)
    (ha : 0<a) (haB : a≤B) :
    (paretoMixture q a B).real {B}=q*a/B ∧ 0<(paretoMixture q a B) {B} := by
  have hB : 0<B:=ha.trans_le haB
  let ν:=paretoMixture q a B
  letI:=pareto_mixture_probability q a B hq0.le hq1 ha
  have he : ν {B}=ν (Ici B) := by
    apply measure_congr
    filter_upwards [pareto_mixture_bounds q a B ha haB] with v hv
    apply propext
    change (v=B ↔ B≤v)
    exact ⟨fun h=>h.ge,fun h=>le_antisymm hv.2 h⟩
  have ht : tail ν B=q*a/B := by
    rw [pareto_mixture_tail q a B B hq0.le hq1 ha,capped_pareto_tail a B B ha]
    by_cases hBa:B≤a
    · have hEq:B=a:=le_antisymm hBa haB
      subst B;simp [ha.le,ha.ne',not_le.mpr ha]
    · simp [hBa,not_le.mpr hB,div_eq_mul_inv,mul_assoc]
  have hr : ν.real {B}=q*a/B := by rw [measureReal_def,he];exact ht
  refine ⟨hr,?_⟩
  have hp : 0<ν.real {B}:=by rw [hr];exact div_pos (mul_pos hq0 ha) hB
  exact ENNReal.toReal_pos_iff.mp hp |>.1

theorem pareto_mixture_scale_of_mean (q a B : ℝ) (hq0 : 0<q) (hq1 : q≤1)
    (ha : 0<a) (haB : a≤B) (hm : mean (paretoMixture q a B)=1) :
    IsScale (paretoMixture q a B) B := by
  rw [IsScale,hm,mul_one]
  constructor
  · apply measure_eq_zero_iff_ae_notMem.mpr
    exact (pareto_mixture_bounds q a B ha haB).mono (fun _ h=>not_lt.mpr h.2)
  · intro k hk
    exact (pareto_mixture_endpoint_atom q a B hq0 hq1 ha haB).2.trans_le
      (measure_mono (singleton_subset_iff.mpr hk))
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem affine_price_profit (ν : Measure ℝ) (c p : ℝ) (hc : c < mean ν) :
    (p-c)*tail ν p=(mean ν-c)*(((p-c)/(mean ν-c))*tail (standardize ν c) ((p-c)/(mean ν-c))) := by
  rw [standardized_tail ν c p hc]
  field_simp [(sub_pos.mpr hc).ne']

theorem standardized_sp (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    spProfit ν c=(mean ν-c)*spProfit (standardize ν c) 0 := by
  have hs : 0 < mean ν-c := sub_pos.mpr hc
  have hstd:=standardized_market ν c hm hc
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨p,rfl⟩
    dsimp only
    rw [affine_price_profit ν c p hc]
    apply mul_le_mul_of_nonneg_left _ hs.le
    simpa only [sub_zero] using price_le_sp (standardize ν c) 0 hstd ((p-c)/(mean ν-c))
  · rw [mul_comm]
    apply (le_div_iff₀ hs).mp
    change spProfit (standardize ν c) 0 ≤ spProfit ν c/(mean ν-c)
    apply csSup_le (range_nonempty _)
    rintro _ ⟨q,rfl⟩
    apply (le_div_iff₀ hs).mpr
    have hp:=price_le_sp ν c hm (c+(mean ν-c)*q)
    have he : ((c+(mean ν-c)*q)-c)/(mean ν-c)=q := by field_simp [hs.ne']; ring
    rw [affine_price_profit ν c _ hc,he] at hp
    simpa only [sub_zero,mul_comm] using hp

theorem standardized_pp (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    ppProfit ν c=(mean ν-c)*ppProfit (standardize ν c) 0 := by
  simp [ppProfit,standardized_mean ν c hm hc]

theorem standardized_margin (ν : Measure ℝ) (c : ℝ) : margin (standardize ν c) 0=1 := by
  simp [margin]
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem mean_positive (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    0 < mean ν := lt_of_le_of_lt hm.cost_nonneg hc

theorem standardized_deviation (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    coefDev (standardize ν c)=coefDev ν/margin ν c := by
  have hs : 0 < mean ν-c := sub_pos.mpr hc
  have hmu:=mean_positive ν c hm hc
  have habs (v : ℝ) : |(v-c)/(mean ν-c)-1|=|v-mean ν|/(mean ν-c) := by
    have he : (v-c)/(mean ν-c)-1=(v-mean ν)/(mean ν-c) := by
      field_simp [hs.ne']
      <;> ring
    rw [he,abs_div,abs_of_pos hs]
  unfold coefDev
  rw [standardized_mean ν c hm hc]
  unfold standardize
  rw [integral_map (μ:=ν) (f:=fun v : ℝ=>|v-1|) (standardizing_measurable ν c).aemeasurable
    (measurable_id.sub_const (1:ℝ)).abs.aestronglyMeasurable]
  simp_rw [habs]
  rw [integral_div]
  unfold margin
  field_simp [hmu.ne',hs.ne']
  <;> ring

theorem scale_threshold (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    c+(mean ν-c)*sc (margin ν c) S=S*mean ν := by
  have hs : mean ν-c≠0 := (sub_pos.mpr hc).ne'
  have hmu : mean ν≠0 := (mean_positive ν c hm hc).ne'
  have hmarg : margin ν c=(mean ν-c)/mean ν := by
    unfold margin
    field_simp [hmu]
  rw [hmarg]
  unfold sc
  field_simp [hmu,hs]
  <;> ring

theorem standardized_scale (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν)
    (S : ℝ) (hS : IsScale ν S) : IsScale (standardize ν c) (sc (margin ν c) S) := by
  have hs : 0 < mean ν-c := sub_pos.mpr hc
  constructor
  · rw [standardized_mean ν c hm hc,mul_one,standardized_Ioi ν c _ hc,scale_threshold ν c S hm hc]
    exact hS.1
  · intro q hq
    rw [standardized_mean ν c hm hc,mul_one] at hq
    rw [standardized_Ioi ν c q hc]
    apply hS.2
    rw [←scale_threshold ν c S hm hc]
    simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hq hs) c

theorem standardized_unbounded (ν : Measure ℝ) (c : ℝ) (hc : c < mean ν)
    (h : Unbounded ν) : Unbounded (standardize ν c) := by
  intro q
  rw [standardized_Ioi ν c q hc]
  exact h _
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem upper_deviation_integral (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c) (hS : IsScale ν S) :
    (∫ v,max (v-mean ν) 0 ∂ν)=∫ p in (mean ν)..(S*mean ν),tail ν p := by
  letI:=hm.isProb
  have hi : Integrable (fun v : ℝ=>max (v-mean ν) 0) ν :=
    (hm.integrable.sub (integrable_const _) ).sup (integrable_const _)
  have hB : 0≤S*mean ν-mean ν := sub_nonneg.mpr (scale_mean_bound ν c S hm hS)
  have hb : (fun v : ℝ=>max (v-mean ν) 0) ≤ᵐ[ν] (fun _=>S*mean ν-mean ν) := by
    filter_upwards [scale_ae_bound ν S hS] with v hv
    exact max_le (sub_le_sub_right hv _) hB
  rw [hi.integral_eq_integral_Ioc_meas_le (Eventually.of_forall (fun _=>le_max_right _ _)) hb]
  have ht : (∫ t in Ioc 0 (S*mean ν-mean ν),ν.real {v : ℝ | t≤ max (v-mean ν) 0})=
      ∫ t in Ioc 0 (S*mean ν-mean ν),tail ν (t+mean ν) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    unfold tail
    rw [measureReal_def]
    congr 2
    ext v
    simp only [mem_setOf_eq,mem_Ici]
    constructor
    · intro hv
      have h:= (le_max_iff.mp hv).resolve_right (not_le.mpr ht.1)
      linarith
    · intro hv
      exact le_max_of_le_left (by linarith)
  rw [ht,←intervalIntegral.integral_of_le hB,intervalIntegral.integral_comp_add_right]
  simp only [zero_add,sub_add_cancel]

theorem lower_deviation_integral (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) :
    (∫ v,max (mean ν-v) 0 ∂ν)=∫ p in c..(mean ν),(1-tail ν p) := by
  letI:=hm.isProb
  have hi : Integrable (fun v : ℝ=>max (mean ν-v) 0) ν :=
    ((integrable_const _).sub hm.integrable ).sup (integrable_const _)
  have hB : 0≤ mean ν-c := sub_nonneg.mpr (mean_ge_cost ν c hm)
  have hb : (fun v : ℝ=>max (mean ν-v) 0) ≤ᵐ[ν] (fun _=>mean ν-c) := by
    filter_upwards [hm.ge_cost] with v hv
    exact max_le (sub_le_sub_left hv _) hB
  rw [hi.integral_eq_integral_Ioc_meas_le (Eventually.of_forall (fun _=>le_max_right _ _)) hb]
  have hae : (fun t : ℝ=>ν.real {v : ℝ | t≤ max (mean ν-v) 0}) =ᵐ[volume.restrict (Ioc 0 (mean ν-c))]
      (fun t=>ν.real {v : ℝ | t< max (mean ν-v) 0}) := by
    filter_upwards [meas_le_ae_eq_meas_lt ν (volume.restrict (Ioc 0 (mean ν-c))) (fun v : ℝ=>max (mean ν-v) 0)] with t ht
    exact congrArg ENNReal.toReal ht
  rw [integral_congr_ae hae]
  have ht : (∫ t in Ioc 0 (mean ν-c),ν.real {v : ℝ | t< max (mean ν-v) 0})=
      ∫ t in Ioc 0 (mean ν-c),(1-tail ν (mean ν-t)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [←lower_tail_complement]
    congr 1
    ext v
    simp only [mem_setOf_eq,mem_Iio,lt_max_iff]
    constructor
    · rintro (hv | hv)
      · linarith
      · linarith [ht.1]
    · intro hv
      left; linarith
  rw [ht,←intervalIntegral.integral_of_le hB,intervalIntegral.integral_comp_sub_left (fun p : ℝ=>1-tail ν p) (mean ν)]
  simp only [sub_sub_cancel,sub_zero]

end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set Filter Topology
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem lower_inverse (w : ℝ) (hw : w≤-1) : lambertWm1 (w*Real.exp w)=w := by
  have hx : w*Real.exp w<0:=mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos w)
  exact ((lambert_spec _ (kernel_minimum w) hx).2.2 w hw rfl).symm

theorem entropy_lower_bound (α D : ℝ) (ha0 : 0<α) (ha1 : α≤1)
    (hD0 : 0≤D) (hD1 : D<1) (hentropy : 1-α+α*Real.log α ≤ D) :
    1 ≤ lowBound 1 D * α := by
  let x : ℝ := (D-1)/Real.exp 1
  have he : 0<Real.exp 1 := Real.exp_pos _
  have hxlo : -1/Real.exp 1≤x := by
    apply (div_le_div_iff_of_pos_right he).mpr
    linarith
  have hx0 : x<0 := div_neg_of_neg_of_pos (by linarith) he
  have hw:=lambert_spec x hxlo hx0
  let u : ℝ := Real.log α-1
  have hu : u≤-1 := by
    have hl : Real.log α≤0 := Real.log_nonpos ha0.le ha1
    dsimp [u]
    linarith
  have heu : Real.exp u=α/Real.exp 1 := by
    dsimp [u]
    rw [Real.exp_sub,Real.exp_log ha0]
  have hku : lambertKernel u≤x := by
    dsimp [lambertKernel,x]
    rw [heu]
    apply (le_div_iff₀ he).mpr
    have hc : u*(α/Real.exp 1)*Real.exp 1=u*α := by field_simp
    rw [hc]
    dsimp [u]
    nlinarith
  have hwu : lambertWm1 x≤u := by
    by_contra h
    have hlt:=kernel_strictAnti hu hw.1 (lt_of_not_ge h)
    change lambertWm1 x*Real.exp (lambertWm1 x)<lambertKernel u at hlt
    rw [hw.2.1] at hlt
    exact (not_lt_of_ge hku) hlt
  have hexp : Real.exp (lambertWm1 x)*Real.exp 1≤α := by
    apply (le_div_iff₀ he).mp
    rw [←heu]
    exact Real.exp_le_exp.mpr hwu
  have hprod:=mul_le_mul_of_nonneg_left hexp (show 0≤ -lambertWm1 x by linarith [hw.1])
  have hid : (-lambertWm1 x)*(Real.exp (lambertWm1 x)*Real.exp 1)=1-D := by
    calc
      _= -(lambertWm1 x*Real.exp (lambertWm1 x))*Real.exp 1 := by ring
      _= -x*Real.exp 1 := by rw [hw.2.1]
      _=1-D := by dsimp [x];field_simp;ring
  rw [hid] at hprod
  change 1≤ (-lambertWm1 ((D/1-1)/Real.exp 1))/(1-D/1)*α
  simp only [div_one]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0<1-D by linarith)).mpr
  simpa [x] using hprod

theorem medium_scalar_bound (α D S : ℝ) (hD : 0<D) (h : D≤α*Real.log S) :
    1 ≤ medBound 1 S D * α := by
  simp only [medBound,sc,mul_one,one_mul,add_sub_cancel_right,div_one]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hD).mpr
  simpa only [one_mul,mul_one,mul_comm] using h
end Queelius.PersonalizedPricing

end

section
open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- The Pricing Inequality (§3.1, p. 9): with zero cost, `F̄(x) ≤ R_SP(F, 0)/x` for every `x > 0`. -/
theorem pricing_inequality (ν : Measure ℝ) (hm : Market ν 0) :
    ∀ x : ℝ, 0 < x → tail ν x ≤ spProfit ν 0 / x := by
  intro x hx
  exact Queelius.PersonalizedPricing.pricing_inequality ν hm x hx

end ValuePersPricing.Deviation

namespace ValuePersPricing.Deviation

/-- Lemma 1 (p. 9): reduction to zero cost and unit mean. With `F_c` the law of
`V_c = (V − c)/(µ − c)`, the standardized market has cost `0` and mean `1`; both profits scale by
`µ − c` (so the ratio `R_PP/R_SP` is unchanged); `M_c = 1`, `D_c = D/M`,
`S_c = (S + M − 1)/M`, and unbounded support is preserved. -/
theorem lemma_1 (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    Market (standardize ν c) 0 ∧
    mean (standardize ν c) = 1 ∧
    spProfit ν c = (mean ν - c) * spProfit (standardize ν c) 0 ∧
    ppProfit ν c = (mean ν - c) * ppProfit (standardize ν c) 0 ∧
    margin (standardize ν c) 0 = 1 ∧
    coefDev (standardize ν c) = coefDev ν / margin ν c ∧
    (∀ S : ℝ, IsScale ν S → IsScale (standardize ν c) (sc (margin ν c) S)) ∧
    (Unbounded ν → Unbounded (standardize ν c)) := by
  exact ⟨Queelius.PersonalizedPricing.standardized_market ν c hm hc,
    Queelius.PersonalizedPricing.standardized_mean ν c hm hc,
    Queelius.PersonalizedPricing.standardized_sp ν c hm hc,
    Queelius.PersonalizedPricing.standardized_pp ν c hm hc,
    Queelius.PersonalizedPricing.standardized_margin ν c,
    Queelius.PersonalizedPricing.standardized_deviation ν c hm hc,
    fun S hS => Queelius.PersonalizedPricing.standardized_scale ν c hm hc S hS,
    Queelius.PersonalizedPricing.standardized_unbounded ν c hc⟩

end ValuePersPricing.Deviation

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

def affineLaw (ν : Measure ℝ) (μ c : ℝ) : Measure ℝ := ν.map (fun v=>c+(μ-c)*v)

theorem affine_measurable (μ c : ℝ) : Measurable (fun v : ℝ=>c+(μ-c)*v) := by fun_prop

theorem affine_market (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0)
    (hc : 0 ≤ c) (hμ : c < μ) : Market (affineLaw ν μ c) c := by
  letI:=hm.isProb
  have hf:=affine_measurable μ c
  refine ⟨Measure.isProbabilityMeasure_map hf.aemeasurable,hc,?_,?_⟩
  · apply (ae_map_iff hf.aemeasurable measurableSet_Ici).mpr
    filter_upwards [hm.ge_cost] with v hv
    have hprod:=mul_nonneg (sub_pos.mpr hμ).le hv
    linarith
  · apply (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr
    exact (integrable_const c).add (hm.integrable.const_mul (μ-c))

theorem affine_mean (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0) (hmean : mean ν=1) :
    mean (affineLaw ν μ c)=μ := by
  letI:=hm.isProb
  unfold mean affineLaw
  rw [integral_map (μ:=ν) (f:=fun v : ℝ=>v) (affine_measurable μ c).aemeasurable measurable_id.aestronglyMeasurable]
  rw [integral_add (integrable_const c) (hm.integrable.const_mul (μ-c)),integral_const_mul]
  change (∫ _ : ℝ,c ∂ν)+(μ-c)*mean ν=μ
  simp [hmean]

theorem affine_standardize (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0)
    (hmean : mean ν=1) (hμ : c < μ) : standardize (affineLaw ν μ c) c=ν := by
  unfold standardize
  rw [affine_mean ν μ c hm hmean]
  unfold affineLaw
  have hg : Measurable (fun v : ℝ=>(v-c)/(μ-c)) := by fun_prop
  rw [Measure.map_map hg (affine_measurable μ c)]
  have he : (fun v : ℝ=>(v-c)/(μ-c)) ∘ (fun v : ℝ=>c+(μ-c)*v)=id := by
    funext v
    dsimp
    field_simp [(sub_pos.mpr hμ).ne']
    ring
  rw [he,Measure.map_id]

theorem affine_margin (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0) (hmean : mean ν=1) :
    margin (affineLaw ν μ c) c=1-c/μ := by rw [margin,affine_mean ν μ c hm hmean]

theorem affine_sp (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0) (hmean : mean ν=1)
    (hc : 0 ≤ c) (hμ : c < μ) : spProfit (affineLaw ν μ c) c=(μ-c)*spProfit ν 0 := by
  have ha:=affine_market ν μ c hm hc hμ
  have hmean':=affine_mean ν μ c hm hmean
  have h:=standardized_sp (affineLaw ν μ c) c ha (by rwa [hmean'])
  rwa [hmean',affine_standardize ν μ c hm hmean hμ] at h

theorem affine_pp (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0) (hmean : mean ν=1) :
    ppProfit (affineLaw ν μ c) c=(μ-c)*ppProfit ν 0 := by
  simp [ppProfit,affine_mean ν μ c hm hmean,hmean]

theorem affine_deviation (ν : Measure ℝ) (μ c : ℝ) (hm : Market ν 0) (hmean : mean ν=1)
    (hc : 0 ≤ c) (hμ : c < μ) : coefDev (affineLaw ν μ c)=(1-c/μ)*coefDev ν := by
  have ha:=affine_market ν μ c hm hc hμ
  have hmean':=affine_mean ν μ c hm hmean
  have hμ':c < mean (affineLaw ν μ c):=by rwa [hmean']
  have hM : 0 < 1-c/μ := sub_pos.mpr ((div_lt_one (lt_of_le_of_lt hc hμ)).mpr hμ)
  have h:=standardized_deviation (affineLaw ν μ c) c ha hμ'
  rw [affine_standardize ν μ c hm hmean hμ,affine_margin ν μ c hm hmean] at h
  exact (eq_div_iff hM.ne').mp h |>.symm.trans (mul_comm _ _)

theorem affine_scale (ν : Measure ℝ) (μ c S : ℝ) (hm : Market ν 0) (hmean : mean ν=1)
    (hc : 0 ≤ c) (hμ : c < μ) (hS : IsScale ν (sc (1-c/μ) S)) :
    IsScale (affineLaw ν μ c) S := by
  have ha:=affine_market ν μ c hm hc hμ
  have hmean':=affine_mean ν μ c hm hmean
  have hμ':c < mean (affineLaw ν μ c):=by rwa [hmean']
  have he (q : ℝ) : ν (Ioi q)=affineLaw ν μ c (Ioi (c+(μ-c)*q)) := by
    have h:=standardized_Ioi (affineLaw ν μ c) c q hμ'
    rwa [affine_standardize ν μ c hm hmean hμ,hmean'] at h
  have hthr : c+(μ-c)*sc (1-c/μ) S=S*μ := by
    have h:=scale_threshold (affineLaw ν μ c) c S ha hμ'
    rwa [hmean',affine_margin ν μ c hm hmean] at h
  constructor
  · rw [hmean',←hthr,←he]
    simpa only [hmean,mul_one] using hS.1
  · intro k hk
    rw [hmean'] at hk
    have hq : (k-c)/(μ-c) < sc (1-c/μ) S := by
      apply (div_lt_iff₀ (sub_pos.mpr hμ)).mpr
      rw [←hthr] at hk
      nlinarith
    have hpos:=hS.2 _ (by simpa only [hmean,mul_one] using hq)
    rw [he] at hpos
    have hid : c+(μ-c)*((k-c)/(μ-c))=k := by
      field_simp [(sub_pos.mpr hμ).ne']
      ring
    rwa [hid] at hpos

theorem affine_tail (ν : Measure ℝ) (μ c p : ℝ) (hm : Market ν 0) (hmean : mean ν=1)
    (hμ : c < μ) : tail (affineLaw ν μ c) (c+(μ-c)*p)=tail ν p := by
  have hmean':=affine_mean ν μ c hm hmean
  have h:=standardized_Ici (affineLaw ν μ c) c p (by rwa [hmean'])
  rw [affine_standardize ν μ c hm hmean hμ,hmean'] at h
  exact congrArg ENNReal.toReal h.symm
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem margin_price_endpoint (ν : Measure ℝ) (c : ℝ) (hμ : mean ν≠0) :
    mean ν*margin ν c+c=mean ν := by
  unfold margin
  field_simp
  ring

theorem scale_price_endpoint (ν : Measure ℝ) (c S : ℝ) (hμ : mean ν≠0) :
    mean ν*(S+margin ν c-1)+c=S*mean ν := by
  unfold margin
  field_simp
  ring

theorem deviation_identities (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hμ : 0 < mean ν) :
    (∀ S : ℝ, IsScale ν S →
      coefDev ν=∫ x in (margin ν c)..(S+margin ν c-1),tail ν (mean ν*x+c)) ∧
    coefDev ν=∫ x in (0 : ℝ)..(margin ν c),(1-tail ν (mean ν*x+c)) := by
  constructor
  · intro S hS
    rw [intervalIntegral.integral_comp_mul_add _ hμ.ne',margin_price_endpoint ν c hμ.ne',
      scale_price_endpoint ν c S hμ.ne',←upper_deviation_integral ν c S hm hS,deviation_upper_part ν c hm]
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  · rw [intervalIntegral.integral_comp_mul_add (fun p=>1-tail ν p) hμ.ne',
      margin_price_endpoint ν c hμ.ne',mul_zero,zero_add,
      ←lower_deviation_integral ν c hm,deviation_lower_part ν c hm]
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem tail_antitone (ν : Measure ℝ) [IsProbabilityMeasure ν] : Antitone (tail ν) := by
  intro x y hxy
  exact measureReal_mono (Ici_subset_Ici.mpr hxy)

theorem tail_at_most_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) : tail ν p ≤ 1 := by
  simpa [tail,measureReal_def] using (measureReal_mono (subset_univ (Ici p)) (μ:=ν))

end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set Filter Topology
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

theorem root_domain (x : ℝ) :
    (∃ w : ℝ,w≤-1 ∧ w*Real.exp w=x) ↔ -1/Real.exp 1≤x ∧ x<0 := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨kernel_minimum w,mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos w)⟩
  · rintro ⟨hx,hx0⟩
    exact lower_root_exists x hx hx0

theorem lambert_junk (x : ℝ) (hx : ¬(-1/Real.exp 1≤x ∧ x<0)) : lambertWm1 x=0 := by
  have he : ¬∃ w : ℝ,w≤-1 ∧ w*Real.exp w=x := by rwa [root_domain]
  simp only [lambertWm1,dif_neg he]

theorem zero_is_outside_branch : lambertWm1 0=0 := lambert_junk 0 (by simp)

theorem positive_input_is_outside_branch : lambertWm1 (2*Real.exp 2)=0 :=
  lambert_junk _ (by have h:=Real.exp_pos (2:ℝ);simp only [not_and_or,not_le,not_lt];exact Or.inr (by positivity))

theorem lower_branch_sample : lambertWm1 (-2*Real.exp (-2))= -2 := lower_inverse (-2) (by norm_num)

theorem branch_point_has_one_root : {w : ℝ | w*Real.exp w= -1/Real.exp 1}.ncard=1 := by
  rw [lambert_all_facts.2.1]
  simp

theorem low_bound_zero_deviation : lowBound 1 0=1 := by
  simp only [lowBound,zero_div,zero_sub,sub_zero,div_one]
  rw [lambert_boundary]
  norm_num
end Queelius.PersonalizedPricing.Controls

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem high_scalar_bound (α B : ℝ) (ha0 : 0<α) (ha1 : α≤1) (hB1 : 1≤B)
    (hbound : 1≤α*(1+Real.log (B/α))) :
    1≤ -lambertWm1 (-1/(Real.exp 1*B))*α := by
  let x : ℝ := -1/(Real.exp 1*B)
  have he : 0<Real.exp 1 := Real.exp_pos _
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB1
  have hden : 0<Real.exp 1*B := mul_pos he hB0
  have hxlo : -1/Real.exp 1≤x := by
    apply (div_le_div_iff₀ he hden).mpr
    nlinarith
  have hx0 : x<0 := div_neg_of_neg_of_pos (by norm_num) hden
  have hw:=lambert_spec x hxlo hx0
  let u : ℝ := Real.log α-Real.log (Real.exp 1*B)
  have hu : u≤-1 := by
    dsimp [u]
    rw [Real.log_mul he.ne' hB0.ne',Real.log_exp]
    linarith [Real.log_le_log ha0 (ha1.trans hB1)]
  have heu : Real.exp u=α/(Real.exp 1*B) := by
    dsimp [u]
    rw [Real.exp_sub,Real.exp_log ha0,Real.exp_log hden]
  have hku : lambertKernel u≤x := by
    dsimp [lambertKernel,x]
    rw [heu]
    apply (le_div_iff₀ hden).mpr
    have hc : u*(α/(Real.exp 1*B))*(Real.exp 1*B)=u*α := by field_simp
    rw [hc]
    dsimp [u]
    rw [Real.log_mul he.ne' hB0.ne',Real.log_exp]
    rw [Real.log_div hB0.ne' ha0.ne'] at hbound
    nlinarith
  have hwu : lambertWm1 x≤u := by
    by_contra h
    have hlt:=kernel_strictAnti hu hw.1 (lt_of_not_ge h)
    change lambertWm1 x*Real.exp (lambertWm1 x)<lambertKernel u at hlt
    rw [hw.2.1] at hlt
    exact (not_lt_of_ge hku) hlt
  have hexp : Real.exp (lambertWm1 x)*(Real.exp 1*B)≤α := by
    apply (le_div_iff₀ hden).mp
    rw [←heu]
    exact Real.exp_le_exp.mpr hwu
  have hprod:=mul_le_mul_of_nonneg_left hexp (show 0≤ -lambertWm1 x by linarith [hw.1])
  have hid : (-lambertWm1 x)*(Real.exp (lambertWm1 x)*(Real.exp 1*B))=1 := by
    calc
      _= -(lambertWm1 x*Real.exp (lambertWm1 x))*(Real.exp 1*B) := by ring
      _= -x*(Real.exp 1*B) := by rw [hw.2.1]
      _=1 := by dsimp [x];field_simp
  rw [hid] at hprod
  exact hprod
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem normalized_upper_integral (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c)
    (hμ : mean ν=1) (hS : IsScale ν S) : coefDev ν=∫ p in (1 : ℝ)..S,tail ν p := by
  rw [deviation_upper_part ν c hm,upper_deviation_integral ν c S hm hS,hμ,mul_one,div_one]

theorem reciprocal_price_integral (α a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫ x in a..b,α/x)=α*Real.log (b/a) := by
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos ha hb]
  rfl

theorem medium_distribution_bound (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0)
    (hμ : mean ν=1) (hS : IsScale ν S) :
    coefDev ν*ppProfit ν 0≤Real.log S*spProfit ν 0 := by
  letI:=hm.isProb
  have hS1 : 1≤S := by simpa only [hμ,mul_one] using scale_mean_bound ν 0 S hm hS
  have hS0 : 0<S := lt_of_lt_of_le zero_lt_one hS1
  have hi : IntervalIntegrable (fun x : ℝ=>spProfit ν 0/x) volume 1 S := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [uIcc_of_le hS1] at hx
    change x ≠ 0
    linarith [hx.1]
  have hle := intervalIntegral.integral_mono_on hS1 (tail_antitone ν).intervalIntegrable hi
    (fun x hx=>pricing_inequality ν hm x (lt_of_lt_of_le zero_lt_one hx.1))
  rw [reciprocal_price_integral _ _ _ zero_lt_one hS0,div_one] at hle
  rw [normalized_upper_integral ν 0 S hm hμ hS]
  simpa only [ppProfit,hμ,sub_zero,mul_one,one_mul,mul_comm] using hle
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem normalized_profit_pos (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν=1) :
    0<spProfit ν 0 := by
  letI:=hm.isProb
  by_contra hn
  have hz : spProfit ν 0=0 := le_antisymm (le_of_not_gt hn) (sp_nonneg ν 0 hm)
  have ht (p : ℝ) (hp : 0<p) : tail ν p=0 := by
    apply le_antisymm _ (tail_nonneg ν p)
    simpa only [hz,zero_div] using pricing_inequality ν hm p hp
  have hi : mean ν=∫ p in Ioi (0 : ℝ),tail ν p := by
    simpa only [mean,tail,measureReal_def,Ici] using
      hm.integrable.integral_eq_integral_meas_le hm.ge_cost
  have hi0 : (∫ p in Ioi (0 : ℝ),tail ν p)=0 := by
    calc
      _=∫ p in Ioi (0 : ℝ),(0 : ℝ) := setIntegral_congr_fun measurableSet_Ioi (fun p hp=>ht p hp)
      _=0 := by simp
  linarith

theorem normalized_deviation_range (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν=1) :
    0≤coefDev ν ∧ coefDev ν<1 := by
  letI:=hm.isProb
  have hi : Integrable (fun v : ℝ=>min v 1) ν := hm.integrable.inf (integrable_const _)
  have hlo : Integrable (fun v : ℝ=>max (1-v) 0) ν :=
    ((integrable_const _).sub hm.integrable).sup (integrable_const _)
  have hn : 0 ≤ᵐ[ν] (fun v : ℝ=>min v 1) := by
    filter_upwards [hm.ge_cost] with v hv
    exact le_min hv zero_le_one
  have hp : 0<(∫ v,min v 1 ∂ν) := by
    by_contra h
    have hz : (∫ v,min v 1 ∂ν)=0 := le_antisymm (le_of_not_gt h) (integral_nonneg_of_ae hn)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    have hv0 : (fun v : ℝ=>v)=ᵐ[ν] 0 := by
      filter_upwards [hae,hm.ge_cost] with v hv hv0
      change min v 1=0 at hv
      change v=0
      rcases le_total v 1 with h | h
      · rw [min_eq_left h] at hv; exact hv
      · rw [min_eq_right h] at hv; norm_num at hv
    have hzμ : mean ν=0 := by rw [mean,integral_congr_ae hv0]; simp
    linarith
  have he : (∫ v,max (1-v) 0 ∂ν)+(∫ v,min v 1 ∂ν)=1 := by
    rw [←integral_add hlo hi]
    have hpoint : (fun v : ℝ=>max (1-v) 0+min v 1)=(fun _ : ℝ=>(1 : ℝ)) := by
      funext v
      rcases le_total v 1 with h | h
      · rw [max_eq_left (by linarith),min_eq_left h]; ring
      · rw [max_eq_right (by linarith),min_eq_right h]; ring
    rw [hpoint]
    simp
  have hd : coefDev ν=∫ v,max (1-v) 0 ∂ν := by
    rw [deviation_lower_part ν 0 hm,hμ,div_one]
  rw [hd]
  exact ⟨integral_nonneg (fun _=>le_max_right _ _),by linarith⟩
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

theorem deterministic_deviation (v : ℝ) : coefDev (Measure.dirac v)=0 := by
  simp [coefDev,mean]

theorem deterministic_scale (v : ℝ) : IsScale (Measure.dirac v) 1 := by
  simp [IsScale,mean,Measure.dirac_apply',measurableSet_Ioi]
  intro k hk
  simp [hk]

theorem deterministic_zero_margin (v : ℝ) (hv : 0 < v) :
    margin (Measure.dirac v) v=0 ∧ coefDev (Measure.dirac v)=0 := by
  simp [margin,mean,hv.ne',deterministic_deviation]

theorem zero_margin_integral_identity (v : ℝ) (hv : 0 < v) :
    coefDev (Measure.dirac v)=∫ x in (0 : ℝ)..(margin (Measure.dirac v) v),
      (1-tail (Measure.dirac v) (mean (Measure.dirac v)*x+v)) := by
  exact (deviation_identities (Measure.dirac v) v (deterministic_market v v hv.le le_rfl)
    (by simpa [mean] using hv)).2

theorem scale_one_integral_identity :
    coefDev (Measure.dirac (1 : ℝ))=∫ x in (1 : ℝ)..1,tail (Measure.dirac (1 : ℝ)) x := by
  simp [deterministic_deviation]

theorem deterministic_low_bound_is_sharp :
    ppProfit (Measure.dirac (1 : ℝ)) 0 =
      lowBound 1 (coefDev (Measure.dirac (1 : ℝ)))*spProfit (Measure.dirac (1 : ℝ)) 0 := by
  rw [deterministic_deviation,low_bound_zero_deviation,deterministic_profit 1 0 (by norm_num) (by norm_num)]
  simp [ppProfit,mean]

theorem strict_tail_complement_fails_at_atom (v : ℝ) :
    (Measure.dirac v).real (Iic v)=1 ∧ 1-tail (Measure.dirac v) v=0 := by
  simp [measureReal_def,Measure.dirac_apply',measurableSet_Iic,measurableSet_Ici,tail]
end Queelius.PersonalizedPricing.Controls

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem sc_one (S : ℝ) : sc 1 S=S := by simp [sc]

theorem threshold_order_normalized (S : ℝ) (hS : 1≤S) :
    0≤deltaL 1 S ∧ deltaL 1 S≤deltaM 1 S ∧ deltaM 1 S≤deltaH 1 S := by
  have hS0 : 0<S:=lt_of_lt_of_le zero_lt_one hS
  have hl : 0≤Real.log S:=Real.log_nonneg hS
  have he : 0<Real.exp 1:=Real.exp_pos _
  let x : ℝ := -1/(Real.exp 1*S)
  have hxlo : -1/Real.exp 1≤x := by
    apply (div_le_div_iff₀ he (mul_pos he hS0)).mpr
    nlinarith
  have hx0 : x<0:=div_neg_of_neg_of_pos (by norm_num) (mul_pos he hS0)
  have hw:=lambert_spec x hxlo hx0
  let u : ℝ := -(1+Real.log S)
  have hu : u≤-1:=by dsimp [u];linarith
  have heu : Real.exp u=1/(Real.exp 1*S) := by
    rw [show u= -(1+Real.log S) by rfl,Real.exp_neg,Real.exp_add,Real.exp_log hS0]
    simp only [one_div]
  have hku : lambertKernel u≤x := by
    dsimp [lambertKernel,x]
    rw [heu]
    rw [mul_one_div]
    apply (div_le_div_iff_of_pos_right (mul_pos he hS0)).mpr
    exact hu
  have hwu : lambertWm1 x≤u := by
    by_contra h
    have hlt:=kernel_strictAnti hu hw.1 (lt_of_not_ge h)
    change lambertWm1 x*Real.exp (lambertWm1 x)<lambertKernel u at hlt
    rw [hw.2.1] at hlt
    exact (not_lt_of_ge hku) hlt
  have hwpos : 0< -lambertWm1 x := by linarith [hw.1]
  have hmid : Real.log S/(-lambertWm1 x)≤Real.log S/(1+Real.log S) := by
    apply div_le_div_of_nonneg_left hl (by linarith)
    dsimp [u] at hwu
    linarith
  have hlast : Real.log S/(1+Real.log S)≤(S-1)/S := by
    apply (div_le_div_iff₀ (by linarith) hS0).mpr
    have hlog:=Real.log_le_sub_one_of_pos hS0
    nlinarith
  have hlow : deltaL 1 S=Real.log S/(-lambertWm1 x) := by
    simp only [deltaL,sc_one,one_mul]
    rw [div_neg,neg_div]
  rw [hlow]
  constructor
  · exact div_nonneg hl hwpos.le
  · simpa only [deltaM,deltaH,sc_one,one_mul,add_sub_cancel_right] using And.intro hmid hlast

theorem threshold_rescaling (M S : ℝ) (hM : M≠0) (hden : S+M-1≠0) :
    deltaL M S=M*deltaL 1 (sc M S) ∧
    deltaM M S=M*deltaM 1 (sc M S) ∧
    deltaH M S=M*deltaH 1 (sc M S) := by
  constructor
  · simp only [deltaL,sc_one,one_mul]
    ring
  constructor
  · simp only [deltaM,sc_one,one_mul]
    ring
  · simp only [deltaH,one_mul,add_sub_cancel_right]
    unfold sc
    field_simp [hM,hden]
    <;> ring

theorem threshold_order (M S : ℝ) (hM : 0<M) (hS : 1≤S) :
    0≤deltaL M S ∧ deltaL M S≤deltaM M S ∧ deltaM M S≤deltaH M S := by
  have hden : 0<S+M-1:=by linarith
  have hsc : 1 ≤ sc M S := by unfold sc;apply (le_div_iff₀ hM).mpr;linarith
  have h:=threshold_order_normalized (sc M S) hsc
  have hr:=threshold_rescaling M S hM.ne' hden.ne'
  rw [hr.1,hr.2.1,hr.2.2]
  exact ⟨mul_nonneg hM.le h.1,mul_le_mul_of_nonneg_left h.2.1 hM.le,
    mul_le_mul_of_nonneg_left h.2.2 hM.le⟩
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem normalized_lower_integral (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν=1) :
    coefDev ν=∫ p in (0 : ℝ)..1,(1-tail ν p) := by
  rw [deviation_lower_part ν 0 hm,lower_deviation_integral ν 0 hm,hμ,div_one]

theorem entropy_distribution_bound (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν=1) :
    1-spProfit ν 0+spProfit ν 0*Real.log (spProfit ν 0)≤coefDev ν := by
  letI:=hm.isProb
  let α:=spProfit ν 0
  have ha0 : 0<α := normalized_profit_pos ν hm hμ
  have ha1 : α≤1 := by simpa only [hμ,sub_zero] using sp_le_surplus ν 0 hm
  have ht (a b : ℝ) : IntervalIntegrable (fun p=>1-tail ν p) volume a b :=
    intervalIntegrable_const.sub (tail_antitone ν).intervalIntegrable
  have hi : IntervalIntegrable (fun x : ℝ=>α/x) volume α 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [uIcc_of_le ha1] at hx
    change x ≠ 0
    linarith [hx.1]
  have hbound := intervalIntegral.integral_mono_on ha1 (intervalIntegrable_const.sub hi) (ht α 1)
    (fun x hx=>sub_le_sub_left (pricing_inequality ν hm x (lt_of_lt_of_le ha0 hx.1)) 1)
  have hn : 0≤∫ p in (0 : ℝ)..α,(1-tail ν p) :=
    intervalIntegral.integral_nonneg ha0.le (fun p _=>sub_nonneg.mpr (tail_at_most_one ν p))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (ht 0 α) (ht α 1)
  rw [←normalized_lower_integral ν hm hμ] at hsplit
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi,intervalIntegral.integral_const,
    reciprocal_price_integral α α 1 ha0 zero_lt_one] at hbound
  simp only [smul_eq_mul,mul_one,Real.log_div (by norm_num : (1:ℝ)≠0) ha0.ne',Real.log_one,zero_sub] at hbound
  dsimp [α] at *
  linarith

theorem low_distribution_bound (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν=1) :
    ppProfit ν 0≤lambertWm1 ((coefDev ν-1)/Real.exp 1)/(coefDev ν-1)*spProfit ν 0 := by
  have ha0:=normalized_profit_pos ν hm hμ
  have ha1 : spProfit ν 0≤1 := by simpa only [hμ,sub_zero] using sp_le_surplus ν 0 hm
  have hd:=normalized_deviation_range ν hm hμ
  have h:=entropy_lower_bound (spProfit ν 0) (coefDev ν) ha0 ha1 hd.1 hd.2
    (entropy_distribution_bound ν hm hμ)
  have he : lowBound 1 (coefDev ν)=lambertWm1 ((coefDev ν-1)/Real.exp 1)/(coefDev ν-1) := by
    unfold lowBound
    simp only [div_one]
    rw [show coefDev ν-1= -(1-coefDev ν) by ring,div_neg]
    rw [neg_div]
  rw [he] at h
  simpa only [ppProfit,hμ,sub_zero] using h
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem comparison_threshold_pos (S : ℝ) (hS : 1<S) :
    0<deltaL 1 S ∧ deltaH 1 S<1 := by
  have he := Real.exp_pos (1:ℝ)
  have hs : 0<S:=lt_trans zero_lt_one hS
  have hx : -1/Real.exp 1≤ -1/(Real.exp 1*S) := by
    apply (div_le_div_iff₀ he (mul_pos he hs)).mpr
    nlinarith
  have hw:= (lambert_spec _ hx (div_neg_of_neg_of_pos (by norm_num) (mul_pos he hs))).1
  constructor
  · simp only [deltaL,sc_one,one_mul]
    rw [neg_div,←div_neg]
    exact div_pos (Real.log_pos hS) (by linarith)
  · simp only [deltaH,one_mul,add_sub_cancel_right]
    exact (div_lt_one hs).mpr (by linarith)

theorem low_comparison_strictMono : StrictMonoOn
    (fun D : ℝ => D * (-lambertWm1 (-(1-D)/Real.exp 1))/(1-D)) (Ioo 0 1) := by
  intro D hD E hE hDE
  have he := Real.exp_pos (1:ℝ)
  have hd : 0<1-D:=by linarith [hD.2]
  have he' : 0<1-E:=by linarith [hE.2]
  have hxD : -(1-D)/Real.exp 1 ∈ Ico (-1/Real.exp 1) 0 := by
    constructor
    · apply (div_le_div_iff_of_pos_right he).mpr;linarith [hD.1]
    · exact div_neg_of_neg_of_pos (by linarith) he
  have hxE : -(1-E)/Real.exp 1 ∈ Ico (-1/Real.exp 1) 0 := by
    constructor
    · apply (div_le_div_iff_of_pos_right he).mpr;linarith [hE.1]
    · exact div_neg_of_neg_of_pos (by linarith) he
  have hwD := (lambert_spec _ hxD.1 hxD.2).1
  have hW := lambert_antitone hxD hxE ((div_le_div_iff_of_pos_right he).mpr (by linarith))
  have hr : D/(1-D)<E/(1-E) := by
    apply (div_lt_div_iff₀ hd he').mpr
    nlinarith
  have hm := mul_lt_mul_of_pos_right hr (show 0< -lambertWm1 (-(1-D)/Real.exp 1) by linarith)
  have hn := mul_le_mul_of_nonneg_left (neg_le_neg hW) (le_of_lt (div_pos hE.1 he'))
  calc
    _ = D/(1-D)*(-lambertWm1 (-(1-D)/Real.exp 1)) := by ring
    _ < E/(1-E)*(-lambertWm1 (-(1-D)/Real.exp 1)) := hm
    _ ≤ E/(1-E)*(-lambertWm1 (-(1-E)/Real.exp 1)) := hn
    _ = _ := by ring

theorem low_comparison_root (S : ℝ) (hS : 1<S) :
    deltaL 1 S * (-lambertWm1 (-(1-deltaL 1 S)/Real.exp 1))/(1-deltaL 1 S)=Real.log S := by
  have hs : 0<S:=lt_trans zero_lt_one hS
  have hl : 0<Real.log S:=Real.log_pos hS
  have he := Real.exp_pos (1:ℝ)
  let x : ℝ := -1/(Real.exp 1*S)
  have hxlo : -1/Real.exp 1≤x := by
    apply (div_le_div_iff₀ he (mul_pos he hs)).mpr;nlinarith
  have hw:=lambert_spec x hxlo (div_neg_of_neg_of_pos (by norm_num) (mul_pos he hs))
  let u : ℝ := -(1+Real.log S)
  have hu : u≤-1:=by dsimp [u];linarith
  have heu : Real.exp u=1/(Real.exp 1*S) := by
    rw [show u= -(1+Real.log S) by rfl,Real.exp_neg,Real.exp_add,Real.exp_log hs]
    simp only [one_div]
  have hku : lambertKernel u≤x := by
    dsimp [lambertKernel,x];rw [heu,mul_one_div]
    exact (div_le_div_iff_of_pos_right (mul_pos he hs)).mpr hu
  have hwu : lambertWm1 x≤u := by
    by_contra h
    have hlt:=kernel_strictAnti hu hw.1 (lt_of_not_ge h)
    change lambertWm1 x*Real.exp (lambertWm1 x)<lambertKernel u at hlt
    rw [hw.2.1] at hlt
    exact (not_lt_of_ge hku) hlt
  let p : ℝ := -lambertWm1 x
  have hp : 0<p:=by dsimp [p];linarith [hw.1]
  have hpL : 1+Real.log S≤p:=by dsimp [p,u] at *;linarith
  have hd : deltaL 1 S=Real.log S/p := by
    simp only [deltaL,sc_one,one_mul];dsimp [p,x];ring
  have hd1 : deltaL 1 S<1 := (threshold_order_normalized S hS.le).2.1.trans_lt
    ((threshold_order_normalized S hS.le).2.2.trans_lt (comparison_threshold_pos S hS).2)
  let v : ℝ := Real.log S-p
  have hv : v≤-1 := by dsimp [v];linarith
  have hev : Real.exp v=S*Real.exp (lambertWm1 x) := by
    dsimp [v,p];rw [sub_neg_eq_add,Real.exp_add,Real.exp_log hs]
  have hkernel : v*Real.exp v= -(1-deltaL 1 S)/Real.exp 1 := by
    rw [hev,hd]
    have heq : p*Real.exp (lambertWm1 x)=1/(Real.exp 1*S) := by
      calc
        _ = -(lambertWm1 x*Real.exp (lambertWm1 x)) := by dsimp [p];ring
        _ = -x := by rw [hw.2.1]
        _ = _ := by dsimp [x];ring
    have hexp : Real.exp (lambertWm1 x)=(1/(Real.exp 1*S))/p := by
      apply (eq_div_iff hp.ne').mpr
      nlinarith [heq]
    rw [hexp]
    dsimp [v]
    field_simp [hp.ne',he.ne',hs.ne']
    <;> ring
  have hvW : lambertWm1 (-(1-deltaL 1 S)/Real.exp 1)=v := by
    rw [←hkernel];exact lower_inverse v hv
  rw [hvW,hd]
  dsimp [v]
  have hden : 1-Real.log S/p≠0:=by rw [←hd];linarith
  field_simp [hp.ne',hden,show p-Real.log S≠0 by linarith]
  <;> ring
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem comparison_high_domain (S D : ℝ) (hS : 1<S) (hD : D ∈ Ioc 0 (deltaH 1 S)) :
    D<1 ∧ 1≤Real.log S/D ∧ -1/Real.exp 1≤ -1/(Real.exp 1*S*(1-D)) := by
  have hs : 0<S:=lt_trans zero_lt_one hS
  have he := Real.exp_pos (1:ℝ)
  have hd : D≤(S-1)/S := by simpa [deltaH] using hD.2
  have hds := (le_div_iff₀ hs).mp hd
  have hd1 : D<1 := hd.trans_lt ((div_lt_one hs).mpr (by linarith))
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [Real.log_inv] at hlog
  have hlow : (S-1)/S≤Real.log S := by
    have hi : (S-1)/S=1-S⁻¹ := by field_simp <;> ring
    rw [hi];linarith
  refine ⟨hd1,(le_div_iff₀ hD.1).mpr (by linarith),?_⟩
  apply (div_le_div_iff₀ he (mul_pos (mul_pos he hs) (by linarith))).mpr
  nlinarith

theorem high_comparison_nonneg_unique (S D : ℝ) (hS : 1<S)
    (hD : D ∈ Ioc 0 (deltaH 1 S)) :
    0≤Real.log S/D+lambertWm1 (-1/(Real.exp 1*S*(1-D))) ∧
    (Real.log S/D+lambertWm1 (-1/(Real.exp 1*S*(1-D)))=0 → D=deltaM 1 S) := by
  have hs : 0<S:=lt_trans zero_lt_one hS
  have he := Real.exp_pos (1:ℝ)
  have hd:=comparison_high_domain S D hS hD
  have hc : 0<S*(1-D):=mul_pos hs (by linarith [hd.1])
  let t : ℝ := Real.log S/D
  let x : ℝ := -1/(Real.exp 1*S*(1-D))
  have hx0 : x<0:=div_neg_of_neg_of_pos (by norm_num) (mul_pos (mul_pos he hs) (by linarith [hd.1]))
  have hw:=lambert_spec x hd.2.2 hx0
  let q : ℝ := Real.log S-t
  have hqexp : Real.exp q=S*Real.exp (-t) := by
    dsimp [q];rw [Real.exp_sub,Real.exp_log hs,Real.exp_neg,div_eq_mul_inv]
  have hDt : D*t=Real.log S := by dsimp [t];field_simp [hD.1.ne']
  have hqkernel : lambertKernel q=(S*(1-D))*((-t)*Real.exp (-t)) := by
    dsimp [lambertKernel];rw [hqexp]
    dsimp [q]
    rw [←hDt]
    ring
  have hxeq : S*(1-D)*x= -1/Real.exp 1 := by dsimp [x];field_simp [hs.ne',(show 1-D≠0 by linarith [hd.1])] <;> ring
  have hmin:=kernel_minimum q
  rw [hqkernel,←hxeq] at hmin
  have hkernel : x≤(-t)*Real.exp (-t):=(mul_le_mul_iff_right₀ hc).mp hmin
  have ht : -t≤-1:=by dsimp [t];linarith [hd.2.1]
  have htw : -t≤lambertWm1 x := by
    by_contra h
    have hh:=kernel_strictAnti hw.1 ht (lt_of_not_ge h)
    change (-t)*Real.exp (-t)<lambertWm1 x*Real.exp (lambertWm1 x) at hh
    rw [hw.2.1] at hh
    exact (not_lt_of_ge hkernel) hh
  constructor
  · change 0≤t+lambertWm1 x;linarith
  · intro hz
    change t+lambertWm1 x=0 at hz
    have hw_eq : lambertWm1 x= -t:=by linarith
    have hke : (-t)*Real.exp (-t)=x:=by rw [←hw_eq];exact hw.2.1
    have hqb : q*Real.exp q= -1/Real.exp 1 := by
      change lambertKernel q= _
      rw [hqkernel,hke,hxeq]
    have hq:=boundary_unique q hqb
    have htd : t=1+Real.log S:=by dsimp [q] at hq;linarith
    have hl : 0<Real.log S:=Real.log_pos hS
    simp only [deltaM,sc_one,one_mul]
    apply (eq_div_iff (show 1+Real.log S≠0 by linarith)).mpr
    rw [←htd]
    exact hDt

theorem high_comparison_root (S : ℝ) (hS : 1<S) :
    Real.log S/deltaM 1 S+lambertWm1 (-1/(Real.exp 1*S*(1-deltaM 1 S)))=0 := by
  have hs : 0<S:=lt_trans zero_lt_one hS
  have hl : 0<Real.log S:=Real.log_pos hS
  have he := Real.exp_pos (1:ℝ)
  let v : ℝ := -(1+Real.log S)
  have hv : v≤-1:=by dsimp [v];linarith
  have hden : 1+Real.log S≠0:=by linarith
  have hd : deltaM 1 S=Real.log S/(1+Real.log S) := by simp only [deltaM,sc_one,one_mul]
  have hkernel : v*Real.exp v= -1/(Real.exp 1*S*(1-deltaM 1 S)) := by
    dsimp [v]
    rw [Real.exp_neg,Real.exp_add,Real.exp_log hs,hd]
    field_simp [hden]
    <;> ring
  rw [←hkernel,lower_inverse v hv,hd]
  dsimp [v]
  field_simp [hl.ne',hden]
  <;> ring
end Queelius.PersonalizedPricing

end

section
open MeasureTheory Set Filter Topology
namespace ValuePersPricing.Deviation

/-- App. A (p. ec1): `w e^w = x` has exactly two real solutions for `x ∈ (−1/e, 0)` and the single
solution `−1` at `x = −1/e` (corrected: the printed "two distinct real solutions" for
`x ∈ [−1/e, 0)` fails at `−1/e`); on `[−1/e, 0)`, `W₋₁(x)` is the unique solution in `(−∞, −1]`;
`W₋₁(−1/e) = −1`; `W₋₁(x) → −∞` as `x → 0⁻`; and `W₋₁` is non-increasing on `[−1/e, 0)`
(asserted on pp. ec2, ec4, ec6). -/
theorem lambertWm1_facts :
    (∀ x ∈ Ioo (-1 / Real.exp 1) 0, {w : ℝ | w * Real.exp w = x}.ncard = 2) ∧
    {w : ℝ | w * Real.exp w = -1 / Real.exp 1} = {-1} ∧
    (∀ x : ℝ, -1 / Real.exp 1 ≤ x → x < 0 →
      lambertWm1 x ≤ -1 ∧ lambertWm1 x * Real.exp (lambertWm1 x) = x ∧
      ∀ w : ℝ, w ≤ -1 → w * Real.exp w = x → w = lambertWm1 x) ∧
    lambertWm1 (-1 / Real.exp 1) = -1 ∧
    Tendsto lambertWm1 (𝓝[<] 0) atBot ∧
    AntitoneOn lambertWm1 (Ico (-1 / Real.exp 1) 0) := by
  exact Queelius.PersonalizedPricing.lambert_all_facts

end ValuePersPricing.Deviation

namespace ValuePersPricing.Deviation

/-- Lemma 3 (p. 14), equation (8): the two integral representations of `D`,
`D = ∫_M^{S+M−1} F̄(µx + c) dx` (for a law of scale `S`) and `D = ∫_0^M (1 − F̄(µx + c)) dx`
(for every law, bounded or not). Margin `M ∈ [0, 1]`: the degenerate case `M = 0` (`c = µ`) is
included. -/
theorem lemma_3 (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hμ : 0 < mean ν) :
    (∀ S : ℝ, IsScale ν S →
      coefDev ν = ∫ x in (margin ν c)..(S + margin ν c - 1), tail ν (mean ν * x + c)) ∧
    coefDev ν = ∫ x in (0 : ℝ)..(margin ν c), (1 - tail ν (mean ν * x + c)) := by
  exact Queelius.PersonalizedPricing.deviation_identities ν c hm hμ

end ValuePersPricing.Deviation

namespace ValuePersPricing.Deviation

/-- Eq. (EC.5) (p. ec2), for `c = 0`, `µ = 1` and every law (no scale hypothesis):
`R_PP/R_SP ≤ W₋₁((D − 1)/e)/(D − 1)`, stated multiplicatively. -/
theorem eq_EC_5 (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν = 1) :
    ppProfit ν 0 ≤
      lambertWm1 ((coefDev ν - 1) / Real.exp 1) / (coefDev ν - 1) * spProfit ν 0 := by
  exact Queelius.PersonalizedPricing.low_distribution_bound ν hm hμ

end ValuePersPricing.Deviation

namespace ValuePersPricing.Deviation

/-- Eq. (EC.6) (p. ec2), for `c = 0`, `µ = 1` and a law of scale `S`: `R_PP/R_SP ≤ log(S)/D`,
stated multiplicatively as `D · R_PP ≤ log(S) · R_SP`. -/
theorem eq_EC_6 (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0) (hμ : mean ν = 1)
    (hS : IsScale ν S) :
    coefDev ν * ppProfit ν 0 ≤ Real.log S * spProfit ν 0 := by
  exact Queelius.PersonalizedPricing.medium_distribution_bound ν S hm hμ hS

end ValuePersPricing.Deviation

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem normalized_deviation_le_scale (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0)
    (hμ : mean ν=1) (hS : IsScale ν S) : coefDev ν≤(S-1)/S := by
  letI:=hm.isProb
  have hS1 : 1≤S := by simpa only [hμ,mul_one] using scale_mean_bound ν 0 S hm hS
  have hS0 : 0<S := lt_of_lt_of_le zero_lt_one hS1
  have hi : Integrable (fun v : ℝ=>max (v-1) 0) ν :=
    (hm.integrable.sub (integrable_const _)).sup (integrable_const _)
  have hb : (fun v : ℝ=>max (v-1) 0) ≤ᵐ[ν] (fun v=>(S-1)/S*v) := by
    filter_upwards [hm.ge_cost,scale_ae_bound ν S hS] with v hv hvS
    simp only [hμ,mul_one] at hvS
    apply max_le
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hS0).mpr
      nlinarith
    · exact mul_nonneg (div_nonneg (sub_nonneg.mpr hS1) hS0.le) hv
  have h:=integral_mono_ae hi (hm.integrable.const_mul _) hb
  rw [integral_const_mul] at h
  change (∫ v,max (v-1) 0 ∂ν)≤(S-1)/S*mean ν at h
  rw [hμ,mul_one] at h
  rw [deviation_upper_part ν 0 hm,hμ,div_one]
  exact h

theorem normalized_tail_bound (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν=1)
    (t : ℝ) (ht : 1≤t) : tail ν t≤1-coefDev ν := by
  letI:=hm.isProb
  have hi : IntervalIntegrable (fun p : ℝ=>1-tail ν p) volume 0 1 :=
    intervalIntegrable_const.sub (tail_antitone ν).intervalIntegrable
  have h:=intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>1-tail ν t) volume 0 1)
    (fun x hx=>sub_le_sub_left (tail_antitone ν (hx.2.trans ht)) 1)
  rw [←normalized_lower_integral ν hm hμ,intervalIntegral.integral_const] at h
  simp only [sub_zero,one_smul] at h
  linarith

theorem split_tail_bound (ν : Measure ℝ) (S t : ℝ) (hm : Market ν 0)
    (hμ : mean ν=1) (hS : IsScale ν S) (ht : 1≤t) (htS : t≤S) :
    coefDev ν≤(t-1)*(1-coefDev ν)+spProfit ν 0*Real.log (S/t) := by
  letI:=hm.isProb
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hS0 : 0<S := lt_of_lt_of_le ht0 htS
  have hi : IntervalIntegrable (fun x : ℝ=>spProfit ν 0/x) volume t S := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [uIcc_of_le htS] at hx
    change x≠0
    linarith [hx.1]
  have hlow:=intervalIntegral.integral_mono_on ht (tail_antitone ν).intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>1-coefDev ν) volume 1 t)
    (fun x hx=>normalized_tail_bound ν hm hμ x hx.1)
  have hupp:=intervalIntegral.integral_mono_on htS (tail_antitone ν).intervalIntegrable hi
    (fun x hx=>pricing_inequality ν hm x (lt_of_lt_of_le ht0 hx.1))
  rw [reciprocal_price_integral _ _ _ ht0 hS0] at hupp
  rw [intervalIntegral.integral_const,smul_eq_mul] at hlow
  have hs : (∫ p in (1 : ℝ)..t,tail ν p)+(∫ p in t..S,tail ν p)=∫ p in (1 : ℝ)..S,tail ν p :=
    intervalIntegral.integral_add_adjacent_intervals (tail_antitone ν).intervalIntegrable
      (tail_antitone ν).intervalIntegrable
  rw [←normalized_upper_integral ν 0 S hm hμ hS] at hs
  linarith
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem pareto_mixture_tail_positive (q a B p : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : 0<a) (hp : 0<p) (hpB : p≤B) :
    tail (paretoMixture q a B) p=if p≤a then q else q*a/p := by
  rw [pareto_mixture_tail q a B p hq0 hq1 ha,capped_pareto_tail a B p ha]
  by_cases hpa:p≤a <;> simp [hpB,hpa,not_le.mpr hp,div_eq_mul_inv,mul_assoc]

theorem pareto_mixture_mean (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a)
    (haB : a≤B) : mean (paretoMixture q a B)=q*a*(1+Real.log (B/a)) := by
  let ν:=paretoMixture q a B
  have hm:=pareto_mixture_market q a B hq0 hq1 ha haB
  letI:=hm.isProb
  have hB0 : 0≤B:=ha.le.trans haB
  have he : mean ν=∫p in (0:ℝ)..B,tail ν p := by
    unfold mean
    rw [hm.integrable.integral_eq_integral_Ioc_meas_le hm.ge_cost
      ((pareto_mixture_bounds q a B ha haB).mono (fun _ h=>h.2))]
    rw [intervalIntegral.integral_of_le hB0]
    rfl
  have hi (u v:ℝ) : IntervalIntegrable (tail ν) volume u v:= (tail_antitone ν).intervalIntegrable
  rw [he,←intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a B)]
  have hlo : (∫p in (0:ℝ)..a,tail ν p)=a*q := by
    calc
      _ = ∫_p in (0:ℝ)..a,q := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha.le
        intro p hp
        rw [pareto_mixture_tail_positive q a B p hq0 hq1 ha hp.1 (hp.2.le.trans haB),if_pos hp.2.le]
      _ = a*q := by simp
  have hhi : (∫p in a..B,tail ν p)=q*a*Real.log (B/a) := by
    calc
      _ = ∫p in a..B,q*a/p := by
        apply intervalIntegral.integral_congr_Ioo_of_le haB
        intro p hp
        rw [pareto_mixture_tail_positive q a B p hq0 hq1 ha (ha.trans hp.1) hp.2.le,if_neg (not_le.mpr hp.1)]
      _ = q*a*Real.log (B/a) := reciprocal_price_integral _ _ _ ha (ha.trans_le haB)
  rw [hlo,hhi]
  ring

theorem pareto_mixture_profit (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a)
    (haB : a≤B) : spProfit (paretoMixture q a B) 0=q*a := by
  let ν:=paretoMixture q a B
  have hm:=pareto_mixture_market q a B hq0 hq1 ha haB
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨p,rfl⟩
    simp only [sub_zero]
    by_cases hp : p≤0
    · exact (mul_nonpos_of_nonpos_of_nonneg hp (tail_nonneg ν p)).trans (mul_nonneg hq0 ha.le)
    · have hp0 : 0<p:=lt_of_not_ge hp
      by_cases hpB:p≤B
      · rw [pareto_mixture_tail_positive q a B p hq0 hq1 ha hp0 hpB]
        split
        next hpa => nlinarith [mul_le_mul_of_nonneg_right hpa hq0]
        next hpa =>
          have he : p*(q*a/p)=q*a := by field_simp [hp0.ne']
          rw [he]
      · rw [pareto_mixture_tail q a B p hq0 hq1 ha,capped_pareto_tail a B p ha]
        simp [hpB,hp,mul_nonneg hq0 ha.le]
  · have h:=price_le_sp ν 0 hm a
    rw [pareto_mixture_tail_positive q a B a hq0 hq1 ha ha haB,if_pos le_rfl] at h
    simpa [sub_zero,mul_comm] using h

theorem pareto_mixture_deviation_below (q a B : ℝ) (hq0 : 0<q) (hq1 : q≤1)
    (ha : 0<a) (ha1 : a≤1) (hB : 1<B)
    (hm : q*a*(1+Real.log (B/a))=1) : coefDev (paretoMixture q a B)=q*a*Real.log B := by
  have haB:=ha1.trans hB.le
  have hmean : mean (paretoMixture q a B)=1:=(pareto_mixture_mean q a B hq0.le hq1 ha haB).trans hm
  rw [normalized_upper_integral _ 0 B (pareto_mixture_market q a B hq0.le hq1 ha haB) hmean
    (pareto_mixture_scale_of_mean q a B hq0 hq1 ha haB hmean)]
  calc
    _ = ∫p in (1:ℝ)..B,q*a/p := by
      apply intervalIntegral.integral_congr_Ioo_of_le hB.le
      intro p hp
      rw [pareto_mixture_tail_positive q a B p hq0.le hq1 ha (zero_lt_one.trans hp.1) hp.2.le,
        if_neg (not_le.mpr (ha1.trans_lt hp.1))]
    _ = q*a*Real.log B := by rw [reciprocal_price_integral _ _ _ zero_lt_one (zero_lt_one.trans hB),div_one]

theorem pareto_mixture_deviation_above (q a B : ℝ) (hq0 : 0<q) (hq1 : q≤1)
    (ha : 1≤a) (haB : a≤B) (hm : q*a*(1+Real.log (B/a))=1) :
    coefDev (paretoMixture q a B)=1-q := by
  have ha0 : 0<a:=zero_lt_one.trans_le ha
  have hmean : mean (paretoMixture q a B)=1:=(pareto_mixture_mean q a B hq0.le hq1 ha0 haB).trans hm
  rw [normalized_lower_integral _ (pareto_mixture_market q a B hq0.le hq1 ha0 haB) hmean]
  calc
    _ = ∫_p in (0:ℝ)..1,1-q := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤1)
      intro p hp
      change 1-tail (paretoMixture q a B) p=1-q
      rw [pareto_mixture_tail_positive q a B p hq0.le hq1 ha0 hp.1 (hp.2.le.trans (ha.trans haB)),
        if_pos (hp.2.le.trans ha)]
    _ = 1-q := by simp
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem medium_tight_parameters (S D : ℝ) (hS : 1<S)
    (hD : D∈Icc (deltaL 1 S) (deltaM 1 S)) :
    let t:=Real.log S/D
    let a:=Real.exp (1+Real.log S-t)
    let q:=(t*a)⁻¹
    0<D ∧ 0<a ∧ a≤1 ∧ 0<q ∧ q≤1 ∧ q*a=D/Real.log S ∧
      q*a*(1+Real.log (S/a))=1 ∧
      a=Real.exp 1*S^(1-1/D) ∧ q=D/Real.log S/Real.exp 1*S^(1/D-1) := by
  dsimp only
  have hs : 0<S:=zero_lt_one.trans hS
  have hl : 0<Real.log S:=Real.log_pos hS
  have hd : 0<D:=(comparison_threshold_pos S hS).1.trans_le hD.1
  let t:=Real.log S/D
  let a:=Real.exp (1+Real.log S-t)
  let q:=(t*a)⁻¹
  have ht : 0<t:=div_pos hl hd
  have ha : 0<a:=Real.exp_pos _
  have htlo : 1+Real.log S≤t := by
    have hmid : D≤Real.log S/(1+Real.log S):=by simpa [deltaM,sc_one] using hD.2
    have hp:= (le_div_iff₀ (show 0<1+Real.log S by linarith)).mp hmid
    exact (le_div_iff₀ hd).mpr (by nlinarith)
  have ha1 : a≤1 := by
    dsimp [a]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have he:=Real.exp_pos (1:ℝ)
  let w:=lambertWm1 (-1/(Real.exp 1*S))
  have hxlo : -1/Real.exp 1≤ -1/(Real.exp 1*S):=by
    apply (div_le_div_iff₀ he (mul_pos he hs)).mpr;nlinarith
  have hw:=lambert_spec (-1/(Real.exp 1*S)) hxlo
    (div_neg_of_neg_of_pos (by norm_num) (mul_pos he hs))
  have hwp : 0< -w:=by dsimp [w];linarith [hw.1]
  have hlow : Real.log S/(-w)≤D:=by simpa only [deltaL,sc_one,one_mul,div_neg,neg_div,w] using hD.1
  have hthi : t≤ -w := by
    have h:= (div_le_iff₀ hwp).mp hlow
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  have hk := kernel_strictAnti.antitoneOn (show w≤-1 from hw.1)
    (show -t≤-1 by linarith) (show w≤-t by linarith)
  change -t*Real.exp (-t)≤w*Real.exp w at hk
  rw [hw.2.1] at hk
  have hexp : a=Real.exp 1*S*Real.exp (-t) := by
    dsimp [a]
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_add,Real.exp_log hs]
  have hprod : 1≤t*a := by
    have hh : 1/(Real.exp 1*S)≤t*Real.exp (-t):=by
      simpa only [neg_mul,neg_div,neg_le_neg_iff] using hk
    have hh':=(div_le_iff₀ (mul_pos he hs)).mp hh
    rw [hexp]
    nlinarith
  have hq : 0<q:=inv_pos.mpr (mul_pos ht ha)
  have hq1 : q≤1:=(inv_le_one₀ (mul_pos ht ha)).mpr hprod
  have hqa : q*a=t⁻¹ := by dsimp [q];field_simp
  have hqa' : q*a=D/Real.log S := by rw [hqa];dsimp [t];rw [inv_div]
  have hid : 1+Real.log (S/a)=t := by
    rw [Real.log_div hs.ne' ha.ne']
    change 1+(Real.log S-Real.log (Real.exp (1+Real.log S-t)))=t
    rw [Real.log_exp];ring
  have hm : q*a*(1+Real.log (S/a))=1 := by rw [hqa,hid,inv_mul_cancel₀ ht.ne']
  have hae : a=Real.exp 1*S^(1-1/D) := by
    rw [Real.rpow_def_of_pos hs,←Real.exp_add]
    dsimp [a,t]
    congr 1
    ring
  have hr : S^(1/D-1)=(S^(1-1/D))⁻¹ := by
    rw [show 1/D-1= -(1-1/D) by ring,Real.rpow_neg hs.le]
  have hqe : q=D/Real.log S/Real.exp 1*S^(1/D-1) := by
    have hh : q=(D/Real.log S)/a := (eq_div_iff ha.ne').mpr hqa'
    rw [hh,hae,hr]
    ring
  exact ⟨hd,ha,ha1,hq,hq1,hqa',hm,hae,hqe⟩
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

/-- Lemma EC.2 (p. ec3), for `S > 1` with `δ_L, δ_M, δ_H` at `M = 1`:
(a) `f(D) = −W₋₁(−(1 − D)/e)/(1 − D) − log(S)/D` is negative on `(0, δ_L)`, positive on
`(δ_L, δ_H]`, and `δ_L` is its unique root in `(0, δ_H]`;
(b) `g(D) = log(S)/D + W₋₁(−1/(e S (1 − D)))` vanishes at `δ_M`, is non-negative on `(0, δ_H]`,
and `δ_M` is its unique root there. -/
theorem comparison_exact (S : ℝ) (hS : 1 < S) :
    ((∀ D ∈ Ioo 0 (deltaL 1 S),
        -lambertWm1 (-(1 - D) / Real.exp 1) / (1 - D) - Real.log S / D < 0) ∧
      (∀ D ∈ Ioc (deltaL 1 S) (deltaH 1 S),
        0 < -lambertWm1 (-(1 - D) / Real.exp 1) / (1 - D) - Real.log S / D) ∧
      -lambertWm1 (-(1 - deltaL 1 S) / Real.exp 1) / (1 - deltaL 1 S)
          - Real.log S / deltaL 1 S = 0 ∧
      (∀ D ∈ Ioc 0 (deltaH 1 S),
        -lambertWm1 (-(1 - D) / Real.exp 1) / (1 - D) - Real.log S / D = 0 →
          D = deltaL 1 S)) ∧
    (Real.log S / deltaM 1 S
          + lambertWm1 (-1 / (Real.exp 1 * S * (1 - deltaM 1 S))) = 0 ∧
      (∀ D ∈ Ioc 0 (deltaH 1 S),
        0 ≤ Real.log S / D + lambertWm1 (-1 / (Real.exp 1 * S * (1 - D)))) ∧
      (∀ D ∈ Ioc 0 (deltaH 1 S),
        Real.log S / D + lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))) = 0 →
          D = deltaM 1 S)) := by
  have hp:=comparison_threshold_pos S hS
  have ho:=threshold_order_normalized S hS.le
  have hl1 : deltaL 1 S<1:=ho.2.1.trans_lt (ho.2.2.trans_lt hp.2)
  have hr:=low_comparison_root S hS
  have hmem : deltaL 1 S ∈ Ioo 0 1:=⟨hp.1,hl1⟩
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · intro D hD
      have hD1 : D<1:=hD.2.trans hl1
      have hlt:=low_comparison_strictMono ⟨hD.1,hD1⟩ hmem hD.2
      dsimp only at hlt
      rw [hr] at hlt
      apply sub_lt_zero.mpr
      apply (lt_div_iff₀ hD.1).mpr
      convert hlt using 1 <;> ring
    · intro D hD
      have hD0 : 0<D:=hp.1.trans hD.1
      have hD1 : D<1:=hD.2.trans_lt hp.2
      have hlt:=low_comparison_strictMono hmem ⟨hD0,hD1⟩ hD.1
      dsimp only at hlt
      rw [hr] at hlt
      apply sub_pos.mpr
      apply (div_lt_iff₀ hD0).mpr
      convert hlt using 1 <;> ring
    · apply sub_eq_zero.mpr
      apply (eq_div_iff hp.1.ne').mpr
      convert hr using 1 <;> ring
    · intro D hD hz
      apply low_comparison_strictMono.injOn ⟨hD.1,hD.2.trans_lt hp.2⟩ hmem
      dsimp only
      rw [hr]
      have heq := (eq_div_iff hD.1.ne').mp (sub_eq_zero.mp hz)
      convert heq using 1 <;> ring
  · exact ⟨high_comparison_root S hS,
      fun D hD=>(high_comparison_nonneg_unique S D hS hD).1,
      fun D hD=>(high_comparison_nonneg_unique S D hS hD).2⟩

end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

-- The excluded zero-deviation endpoint really breaks the nonnegative comparison
-- under Lean's totalized division; it cannot be silently added to the interval.
theorem high_at_zero_negative (S : ℝ) (hS : 1<S) :
    Real.log S/(0:ℝ)+lambertWm1 (-1/(Real.exp 1*S*(1-0)))<0 := by
  have hs : 0<S:=lt_trans zero_lt_one hS
  have he:=Real.exp_pos (1:ℝ)
  have hx : -1/Real.exp 1≤ -1/(Real.exp 1*S) := by
    apply (div_le_div_iff₀ he (mul_pos he hs)).mpr;nlinarith
  have hw := (lambert_spec _ hx (div_neg_of_neg_of_pos (by norm_num) (mul_pos he hs))).1
  simpa using (show lambertWm1 (-1/(Real.exp 1*S))<0 by linarith)

theorem low_at_zero_value (S : ℝ) :
    -lambertWm1 (-(1-(0:ℝ))/Real.exp 1)/(1-0)-Real.log S/0=1 := by
  simpa using congrArg Neg.neg lambert_boundary

-- At the closed upper endpoint the argument is exactly the branch point.
theorem high_at_upper_endpoint (S : ℝ) (hS : 1<S) :
    lambertWm1 (-1/(Real.exp 1*S*(1-deltaH 1 S)))= -1 := by
  have hs : S≠0:=ne_of_gt (lt_trans zero_lt_one hS)
  have hi : -1/(Real.exp 1*S*(1-deltaH 1 S))= -1/Real.exp 1 := by
    simp only [deltaH,one_mul,add_sub_cancel_right]
    field_simp [hs]
    <;> ring
  rw [hi]
  exact lambert_boundary

-- A concrete interior equality check: scale e has medium threshold 1/2.
theorem high_e_half :
    Real.log (Real.exp 1)/(1/2:ℝ)+
      lambertWm1 (-1/(Real.exp 1*Real.exp 1*(1-(1/2:ℝ))))=0 := by
  have he1 : 1<Real.exp (1:ℝ):=by simpa using Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
  have hd : deltaM 1 (Real.exp 1)=(1/2:ℝ) := by norm_num [deltaM,sc_one]
  simpa only [hd] using high_comparison_root (Real.exp 1) he1
end Queelius.PersonalizedPricing.Controls

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem high_tight_parameters (S D : ℝ) (hS : 1<S)
    (hD : D∈Icc (deltaM 1 S) (deltaH 1 S)) :
    let q:=1-D
    let t:= -lambertWm1 (-1/(Real.exp 1*S*(1-D)))
    let a:=t⁻¹/q
    0<q ∧ q≤1 ∧ 0<t ∧ 1≤a ∧ a≤S ∧ q*a*(1+Real.log (S/a))=1 := by
  dsimp only
  have hs : 0<S:=zero_lt_one.trans hS
  have hl : 0<Real.log S:=Real.log_pos hS
  have hd0 : 0<D:=((comparison_threshold_pos S hS).1.trans_le
    (threshold_order_normalized S hS.le).2.1).trans_le hD.1
  have hd:=comparison_high_domain S D hS ⟨hd0,hD.2⟩
  let q:=1-D
  let w:=lambertWm1 (-1/(Real.exp 1*S*(1-D)))
  let t:= -w
  let a:=t⁻¹/q
  have hq : 0<q:=by dsimp [q];linarith [hd.1]
  have hq1 : q≤1:=by dsimp [q];linarith
  have he:=Real.exp_pos (1:ℝ)
  have hden : 0<Real.exp 1*S*q:=mul_pos (mul_pos he hs) hq
  have hw:=lambert_spec (-1/(Real.exp 1*S*q)) hd.2.2
    (div_neg_of_neg_of_pos (by norm_num) hden)
  have ht1 : 1≤t:=by dsimp [t,w,q];linarith [hw.1]
  have ht : 0<t:=zero_lt_one.trans_le ht1
  have halpha : t⁻¹≤1:= (inv_le_one₀ ht).mpr ht1
  have hSq : 1≤S*q := by
    have hh : D≤(S-1)/S:=by simpa [deltaH] using hD.2
    have hh':= (le_div_iff₀ hs).mp hh
    dsimp [q];nlinarith
  have haS : a≤S := by
    dsimp [a]
    exact (div_le_iff₀ hq).mpr (halpha.trans hSq)
  have hcomp:= (high_comparison_nonneg_unique S D hS ⟨hd0,hD.2⟩).1
  have htw : t≤Real.log S/D := by dsimp [t,w];linarith
  have hmid : Real.log S/(1+Real.log S)≤D:=by simpa [deltaM,sc_one] using hD.1
  have hmid' := (div_le_iff₀ (show 0<1+Real.log S by linarith)).mp hmid
  have hprod : t*q≤1 := by
    have hh:=mul_le_mul_of_nonneg_right htw hq.le
    have hh2 : (Real.log S/D)*q≤1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_one hd0).mpr
      dsimp [q]
      nlinarith
    exact hh.trans hh2
  have ha1 : 1≤a := by
    dsimp [a]
    apply (le_div_iff₀ hq).mpr
    simp only [one_mul]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hwe : t*Real.exp w=1/(Real.exp 1*S*q) := by
    dsimp [t]
    have h:=hw.2.1
    change w*Real.exp w= -1/(Real.exp 1*S*q) at h
    rw [neg_mul,h]
    ring
  have hlog:=congrArg Real.log hwe
  rw [Real.log_mul ht.ne' (Real.exp_pos w).ne',Real.log_exp,
    Real.log_div one_ne_zero hden.ne',Real.log_one,
    Real.log_mul (mul_pos he hs).ne' hq.ne',Real.log_mul he.ne' hs.ne',Real.log_exp] at hlog
  have ha0 : 0<a:=zero_lt_one.trans_le ha1
  have hloga : Real.log a= -Real.log t-Real.log q := by
    dsimp [a]
    rw [Real.log_div (inv_ne_zero ht.ne') hq.ne',Real.log_inv]
  have hidentity : 1+Real.log (S/a)=t := by
    rw [Real.log_div hs.ne' ha0.ne',hloga]
    dsimp [t]
    linarith
  have hqa : q*a=t⁻¹ := by dsimp [a];field_simp
  have hmean : q*a*(1+Real.log (S/a))=1 := by
    rw [hqa,hidentity,inv_mul_cancel₀ ht.ne']
  exact ⟨hq,hq1,ht,ha1,haS,hmean⟩
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem high_distribution_bound_closed (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0)
    (hμ : mean ν=1) (hS : IsScale ν S) (hS1 : 1<S)
    (hD : deltaM 1 S≤coefDev ν) :
    ppProfit ν 0≤ -lambertWm1 (-1/(Real.exp 1*S*(1-coefDev ν)))*spProfit ν 0 := by
  let D:=coefDev ν
  let α:=spProfit ν 0
  have ha0 : 0<α:=normalized_profit_pos ν hm hμ
  have ha1 : α≤1 := by simpa only [hμ,sub_zero] using sp_le_surplus ν 0 hm
  have hD1 : D<1 := (normalized_deviation_range ν hm hμ).2
  have hc : 0<1-D := by linarith
  have hl : 0<Real.log S := Real.log_pos hS1
  have hS0 : 0<S := lt_trans zero_lt_one hS1
  have hdmax : D≤(S-1)/S := normalized_deviation_le_scale ν S hm hμ hS
  have hB : 1≤S*(1-D) := by
    have h:=(le_div_iff₀ hS0).mp hdmax
    nlinarith
  have hth : Real.log S≤D*(1+Real.log S) := by
    apply (div_le_iff₀ (by linarith : 0<1+Real.log S)).mp
    simpa only [deltaM,sc,one_mul,add_sub_cancel_right,div_one] using hD
  have hmD : D≤α*Real.log S := by
    have h:=medium_distribution_bound ν S hm hμ hS
    simpa only [ppProfit,hμ,sub_zero,mul_one,mul_comm,one_mul] using h
  have halow : 1-D≤α := by nlinarith
  have ht : 1≤α/(1-D) := by apply (le_div_iff₀ hc).mpr;simpa using halow
  have htS : α/(1-D)≤S := by apply (div_le_iff₀ hc).mpr;nlinarith
  have hsplit:=split_tail_bound ν S (α/(1-D)) hm hμ hS ht htS
  have hid : (α/(1-D)-1)*(1-D)=α-(1-D) := by field_simp <;> ring
  have hquot : S/(α/(1-D))=(S*(1-D))/α := by field_simp
  change D≤(α/(1-D)-1)*(1-D)+α*Real.log (S/(α/(1-D))) at hsplit
  rw [hid,hquot] at hsplit
  have hbound : 1≤α*(1+Real.log ((S*(1-D))/α)) := by nlinarith
  have h:=high_scalar_bound α (S*(1-D)) ha0 ha1 hB hbound
  simpa only [ppProfit,hμ,sub_zero,mul_assoc] using h

theorem high_distribution_bound (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0)
    (hμ : mean ν=1) (hS : IsScale ν S) (hD : deltaM 1 S<coefDev ν) :
    ppProfit ν 0≤ -lambertWm1 (-1/(Real.exp 1*S*(1-coefDev ν)))*spProfit ν 0 := by
  have hSge : 1≤S := by simpa only [hμ,mul_one] using scale_mean_bound ν 0 S hm hS
  have hS1 : 1<S := by
    by_contra h
    have he : S=1 := le_antisymm (not_lt.mp h) hSge
    rw [he] at hD hS
    have hb:=normalized_deviation_le_scale ν 1 hm hμ hS
    norm_num [deltaM,sc] at hD hb
    linarith
  exact high_distribution_bound_closed ν S hm hμ hS hS1 hD.le
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem market_margin_pos (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c< mean ν) :
    0< margin ν c := by
  have hμ:=mean_positive ν c hm hc
  unfold margin
  have hdiv : c/mean ν<1 := (div_lt_one hμ).mpr hc
  linarith

theorem full_deviation_partition (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c)
    (hc : c< mean ν) (hS : IsScale ν S) :
    0≤coefDev ν ∧ coefDev ν≤deltaH (margin ν c) S ∧
    0≤deltaL (margin ν c) S ∧ deltaL (margin ν c) S≤deltaM (margin ν c) S ∧
    deltaM (margin ν c) S≤deltaH (margin ν c) S := by
  have hμ:=mean_positive ν c hm hc
  have hM:=market_margin_pos ν c hm hc
  have hS1 : 1≤S := by
    have h:=scale_mean_bound ν c S hm hS
    nlinarith
  have hnorm:=standardized_market ν c hm hc
  have hmean:=standardized_mean ν c hm hc
  have hscale:=standardized_scale ν c hm hc S hS
  have hd:=normalized_deviation_range (standardize ν c) hnorm hmean
  have hmax:=normalized_deviation_le_scale (standardize ν c) (sc (margin ν c) S) hnorm hmean hscale
  rw [standardized_deviation ν c hm hc] at hd hmax
  have hnonneg : 0≤coefDev ν := by simpa using (le_div_iff₀ hM).mp hd.1
  have hH : coefDev ν≤deltaH (margin ν c) S := by
    have h:= (div_le_iff₀ hM).mp hmax
    have hr:=threshold_rescaling (margin ν c) S hM.ne' (show S+margin ν c-1≠0 by linarith)
    rw [hr.2.2]
    simpa only [deltaH,one_mul,add_sub_cancel_right,mul_comm] using h
  exact ⟨hnonneg,hH,threshold_order (margin ν c) S hM hS1⟩
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

def lowMixture (q a B : ℝ) : Measure ℝ :=
  ENNReal.ofReal q • cappedPareto a B + ENNReal.ofReal (1-q) • cappedPareto a 1

theorem low_mixture_probability (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a) :
    IsProbabilityMeasure (lowMixture q a B) := by
  letI:=capped_pareto_probability a B ha
  letI:=capped_pareto_probability a 1 ha
  constructor
  simp only [lowMixture,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add hq0 (by linarith)]
  norm_num

theorem low_mixture_tail (q a B p : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a) :
    tail (lowMixture q a B) p=q*tail (cappedPareto a B) p+(1-q)*tail (cappedPareto a 1) p := by
  letI:=capped_pareto_probability a B ha
  letI:=capped_pareto_probability a 1 ha
  unfold tail lowMixture
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hq0,ENNReal.toReal_ofReal (show 0≤1-q by linarith)]

theorem low_mixture_bounds (q a B : ℝ) (ha : 0<a) (ha1 : a≤1) (hB : 1≤B) :
    ∀ᵐv ∂lowMixture q a B,a≤v ∧ v≤B := by
  unfold lowMixture
  apply ae_add_measure_iff.mpr
  constructor
  · apply Measure.ae_smul_measure
    exact capped_pareto_bounds a B ha (ha1.trans hB)
  · apply Measure.ae_smul_measure
    exact (capped_pareto_bounds a 1 ha ha1).mono (fun _ h=>⟨h.1,h.2.trans hB⟩)

theorem low_mixture_market (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a)
    (ha1 : a≤1) (hB : 1≤B) : Market (lowMixture q a B) 0 := by
  letI:=low_mixture_probability q a B hq0 hq1 ha
  have hb:=low_mixture_bounds q a B ha ha1 hB
  refine ⟨inferInstance,le_rfl,hb.mono (fun _ h=>ha.le.trans h.1),?_⟩
  apply (integrable_const B).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hb] with v hv
  simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (ha.le.trans hv.1)] using hv.2

theorem low_mixture_tail_formula (q a B p : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : 0<a) (ha1 : a≤1) (hB : 1≤B) :
    tail (lowMixture q a B) p=if p≤a then 1 else if p≤1 then a/p else if p≤B then q*a/p else 0 := by
  rw [low_mixture_tail q a B p hq0 hq1 ha,capped_pareto_tail a B p ha,capped_pareto_tail a 1 p ha]
  by_cases hpa:p≤a
  · simp [hpa,hpa.trans ha1,(hpa.trans ha1).trans hB]
  · by_cases hp1:p≤1
    · simp [hpa,hp1,hp1.trans hB];ring
    · by_cases hpB:p≤B <;> simp [hpa,hp1,hpB,div_eq_mul_inv,mul_assoc]

theorem low_mixture_mean (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a)
    (ha1 : a≤1) (hB : 1≤B) : mean (lowMixture q a B)=a*(1-Real.log a)+q*a*Real.log B := by
  let ν:=lowMixture q a B
  have hm:=low_mixture_market q a B hq0 hq1 ha ha1 hB
  letI:=hm.isProb
  have he : mean ν=∫p in (0:ℝ)..B,tail ν p := by
    unfold mean
    rw [hm.integrable.integral_eq_integral_Ioc_meas_le hm.ge_cost
      ((low_mixture_bounds q a B ha ha1 hB).mono (fun _ h=>h.2))]
    rw [intervalIntegral.integral_of_le (zero_le_one.trans hB)]
    rfl
  have hi (u v:ℝ) : IntervalIntegrable (tail ν) volume u v:=(tail_antitone ν).intervalIntegrable
  rw [he,←intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 B),
    ←intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a 1)]
  have hlo : (∫p in (0:ℝ)..a,tail ν p)=a := by
    calc
      _ = ∫_p in (0:ℝ)..a,(1:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha.le
        intro p hp
        rw [low_mixture_tail_formula q a B p hq0 hq1 ha ha1 hB,if_pos hp.2.le]
      _ = a := by simp
  have hmid : (∫p in a..(1:ℝ),tail ν p)= -a*Real.log a := by
    calc
      _ = ∫p in a..(1:ℝ),a/p := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha1
        intro p hp
        rw [low_mixture_tail_formula q a B p hq0 hq1 ha ha1 hB,if_neg (not_le.mpr hp.1),if_pos hp.2.le]
      _ = -a*Real.log a := by rw [reciprocal_price_integral _ _ _ ha zero_lt_one,one_div,Real.log_inv];ring
  have hhi : (∫p in (1:ℝ)..B,tail ν p)=q*a*Real.log B := by
    calc
      _ = ∫p in (1:ℝ)..B,q*a/p := by
        apply intervalIntegral.integral_congr_Ioo_of_le hB
        intro p hp
        rw [low_mixture_tail_formula q a B p hq0 hq1 ha ha1 hB,
          if_neg (not_le.mpr (ha1.trans_lt hp.1)),if_neg (not_le.mpr hp.1),if_pos hp.2.le]
      _ = q*a*Real.log B := by rw [reciprocal_price_integral _ _ _ zero_lt_one (zero_lt_one.trans_le hB),div_one]
  rw [hlo,hmid,hhi];ring

theorem low_mixture_profit (q a B : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (ha : 0<a)
    (ha1 : a≤1) (hB : 1≤B) : spProfit (lowMixture q a B) 0=a := by
  let ν:=lowMixture q a B
  have hm:=low_mixture_market q a B hq0 hq1 ha ha1 hB
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨p,rfl⟩
    simp only [sub_zero]
    by_cases hp:p≤0
    · exact (mul_nonpos_of_nonpos_of_nonneg hp (tail_nonneg ν p)).trans ha.le
    · have hp0 : 0<p:=lt_of_not_ge hp
      rw [low_mixture_tail_formula q a B p hq0 hq1 ha ha1 hB]
      split
      next hpa => simpa using hpa
      next hpa =>
        split
        next hp1 => field_simp;exact le_rfl
        next hp1 =>
          split
          next hpB =>
            have he : p*(q*a/p)=q*a:=by field_simp
            rw [he];nlinarith
          next hpB => simp [ha.le]
  · have h:=price_le_sp ν 0 hm a
    rw [low_mixture_tail_formula q a B a hq0 hq1 ha ha1 hB,if_pos le_rfl] at h
    simpa using h
end Queelius.PersonalizedPricing

end

section
noncomputable section
open Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem low_tight_parameters (S D : ℝ) (hS : 1<S) (hD : D∈Ioc 0 (deltaL 1 S)) :
    let a:=(lambertWm1 ((D-1)/Real.exp 1)/(D-1))⁻¹
    let b:=D/Real.log S
    0<a ∧ a≤1 ∧ 0<b ∧ b≤a ∧ a*(1-Real.log a)+D=1 := by
  dsimp only
  have hd:=hD.1
  have hl:=Real.log_pos hS
  have ho:=threshold_order_normalized S hS.le
  have hd1 : D<1:=hD.2.trans_lt (ho.2.1.trans ho.2.2 |>.trans_lt (comparison_threshold_pos S hS).2)
  have he:=Real.exp_pos (1:ℝ)
  let w:=lambertWm1 ((D-1)/Real.exp 1)
  let a:=(w/(D-1))⁻¹
  have hxlo : -1/Real.exp 1≤(D-1)/Real.exp 1:=by
    apply (div_le_div_iff_of_pos_right he).mpr;linarith
  have hw:=lambert_spec ((D-1)/Real.exp 1) hxlo (div_neg_of_neg_of_pos (by linarith) he)
  have hw0 : w<0:=by dsimp [w];linarith [hw.1]
  have hr : 0<w/(D-1):=div_pos_of_neg_of_neg hw0 (by linarith)
  have ha : 0<a:=inv_pos.mpr hr
  have hwa : w*a=D-1 := by dsimp [a];field_simp [hw0.ne]
  have hae : a=Real.exp (w+1) := by
    apply (mul_left_cancel₀ hw0.ne)
    rw [hwa,Real.exp_add,←mul_assoc]
    change D-1=(w*Real.exp w)*Real.exp 1
    rw [hw.2.1,div_mul_cancel₀ _ he.ne']
  have ha1 : a≤1 := by rw [hae];exact Real.exp_le_one_iff.mpr (by have hh : w≤-1:=hw.1;linarith)
  have hmean : a*(1-Real.log a)+D=1 := by
    have hloga : Real.log a=w+1:=by rw [hae,Real.log_exp]
    rw [hloga];nlinarith [hwa]
  have hcomp : w/(D-1)≤Real.log S/D := by
    have heq : -(1-D)/Real.exp 1=(D-1)/Real.exp 1:=by ring
    rcases lt_or_eq_of_le hD.2 with hlt|heD
    · have h:=(comparison_exact S hS).1.1 D ⟨hd,hlt⟩
      rw [heq] at h
      have hh : -lambertWm1 ((D-1)/Real.exp 1)/(1-D)=w/(D-1):=by rw [show 1-D= -(D-1) by ring,neg_div_neg_eq]
      rw [hh] at h
      linarith
    · subst D
      have h:=(comparison_exact S hS).1.2.2.1
      rw [heq] at h
      have hh : -lambertWm1 ((deltaL 1 S-1)/Real.exp 1)/(1-deltaL 1 S)=w/(deltaL 1 S-1):=by rw [show 1-deltaL 1 S= -(deltaL 1 S-1) by ring,neg_div_neg_eq]
      rw [hh] at h
      linarith
  have hba : D/Real.log S≤a := by
    have h:=(le_div_iff₀ hd).mp hcomp
    have hp:=mul_le_mul_of_nonneg_right h ha.le
    have hinv : w/(D-1)*a=1:=by dsimp [a];exact mul_inv_cancel₀ hr.ne'
    apply (div_le_iff₀ hl).mpr
    nlinarith [hinv]
  exact ⟨ha,ha1,div_pos hd hl,hba,hmean⟩
end Queelius.PersonalizedPricing

end

section
theorem ValuePersPricing.Deviation.lemma_EC_2 : (
∀ (S : Real),
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S →
    And
      (And
        (∀ (D : Real),
          @Membership.mem Real (Set Real) (@Set.instMembership Real)
              (@Set.Ioo Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                (ValuePersPricing.Deviation.deltaL (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S))
              D →
            @LT.lt Real Real.instLT
              (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@Neg.neg Real Real.instNeg
                    (ValuePersPricing.Deviation.lambertWm1
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@Neg.neg Real Real.instNeg
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))
                        (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))))
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (Real.log S) D))
              (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
        (And
          (∀ (D : Real),
            @Membership.mem Real (Set Real) (@Set.instMembership Real)
                (@Set.Ioc Real Real.instPreorder
                  (ValuePersPricing.Deviation.deltaL (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    S)
                  (ValuePersPricing.Deviation.deltaH (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    S))
                D →
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                    (@Neg.neg Real Real.instNeg
                      (ValuePersPricing.Deviation.lambertWm1
                        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                          (@Neg.neg Real Real.instNeg
                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))
                          (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))))
                    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))
                  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                    (Real.log S) D)))
          (And
            (@Eq Real
              (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@Neg.neg Real Real.instNeg
                    (ValuePersPricing.Deviation.lambertWm1
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@Neg.neg Real Real.instNeg
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                            (ValuePersPricing.Deviation.deltaL
                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S)))
                        (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))))
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    (ValuePersPricing.Deviation.deltaL (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                      S)))
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (Real.log S)
                  (ValuePersPricing.Deviation.deltaL (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    S)))
              (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
            (∀ (D : Real),
              @Membership.mem Real (Set Real) (@Set.instMembership Real)
                  (@Set.Ioc Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                    (ValuePersPricing.Deviation.deltaH (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                      S))
                  D →
                @Eq Real
                    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@Neg.neg Real Real.instNeg
                          (ValuePersPricing.Deviation.lambertWm1
                            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                              (@Neg.neg Real Real.instNeg
                                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))
                              (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))))
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (Real.log S) D))
                    (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
                  @Eq Real D
                    (ValuePersPricing.Deviation.deltaL (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                      S)))))
      (And
        (@Eq Real
          (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Real.log S)
              (ValuePersPricing.Deviation.deltaM (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S))
            (ValuePersPricing.Deviation.lambertWm1
              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                    (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) S)
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    (ValuePersPricing.Deviation.deltaM (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                      S))))))
          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
        (And
          (∀ (D : Real),
            @Membership.mem Real (Set Real) (@Set.instMembership Real)
                (@Set.Ioc Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                  (ValuePersPricing.Deviation.deltaH (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    S))
                D →
              @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                    (Real.log S) D)
                  (ValuePersPricing.Deviation.lambertWm1
                    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                      (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                          (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) S)
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))))))
          (∀ (D : Real),
            @Membership.mem Real (Set Real) (@Set.instMembership Real)
                (@Set.Ioc Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                  (ValuePersPricing.Deviation.deltaH (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    S))
                D →
              @Eq Real
                  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                      (Real.log S) D)
                    (ValuePersPricing.Deviation.lambertWm1
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                            (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) S)
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D)))))
                  (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
                @Eq Real D
                  (ValuePersPricing.Deviation.deltaM (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    S))))
) := @Queelius.PersonalizedPricing.comparison_exact

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem pareto_mixture_tail_nonnegative (q a B x : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : 0<a) (haB : a≤B) (hx : 0≤x) :
    tail (paretoMixture q a B) x=
      if x=0 then 1 else if x≤a then q else if x≤B then q*a/x else 0 := by
  by_cases hx0:x=0
  · subst x
    rw [pareto_mixture_tail q a B 0 hq0 hq1 ha,capped_pareto_tail a B 0 ha]
    have hB0:=ha.le.trans haB
    simp [hB0,ha.le]
  · have hxpos : 0<x:=lt_of_le_of_ne hx (Ne.symm hx0)
    by_cases hxa:x≤a
    · rw [pareto_mixture_tail_positive q a B x hq0 hq1 ha hxpos (hxa.trans haB)]
      simp [hx0,hxa]
    · by_cases hxB:x≤B
      · rw [pareto_mixture_tail_positive q a B x hq0 hq1 ha hxpos hxB]
        simp [hx0,hxa,hxB]
      · rw [pareto_mixture_tail q a B x hq0 hq1 ha,capped_pareto_tail a B x ha]
        simp [hx0,hxa,hxB,not_le.mpr hxpos]

theorem high_tight_law (S D : ℝ) (hS : 1<S) (hD : D∈Icc (deltaM 1 S) (deltaH 1 S)) :
    ∃ν:Measure ℝ,Market ν 0 ∧ mean ν=1 ∧ IsScale ν S ∧ coefDev ν=D ∧
      (∀x:ℝ,0≤x → tail ν x=
        if x=0 then 1 else if x≤(-lambertWm1 (-1/(Real.exp 1*S*(1-D))))⁻¹/(1-D) then 1-D
        else if x≤S then (-lambertWm1 (-1/(Real.exp 1*S*(1-D))))⁻¹/x else 0) ∧
      ppProfit ν 0= -lambertWm1 (-1/(Real.exp 1*S*(1-D)))*spProfit ν 0 := by
  let q:=1-D
  let t:= -lambertWm1 (-1/(Real.exp 1*S*(1-D)))
  let a:=t⁻¹/q
  obtain ⟨hq,hq1,ht,ha1,haS,he⟩:=high_tight_parameters S D hS hD
  change 0<q at hq
  change q≤1 at hq1
  change 0<t at ht
  change 1≤a at ha1
  change a≤S at haS
  change q*a*(1+Real.log (S/a))=1 at he
  have ha : 0<a:=zero_lt_one.trans_le ha1
  let ν:=paretoMixture q a S
  have hm:=pareto_mixture_market q a S hq.le hq1 ha haS
  have hmean : mean ν=1:=(pareto_mixture_mean q a S hq.le hq1 ha haS).trans he
  have hscale:=pareto_mixture_scale_of_mean q a S hq hq1 ha haS hmean
  have hdev : coefDev ν=D := by
    rw [pareto_mixture_deviation_above q a S hq hq1 ha1 haS he]
    dsimp [q];ring
  have hqa : q*a=t⁻¹ := by dsimp [a];field_simp
  refine ⟨ν,hm,hmean,hscale,hdev,?_,?_⟩
  · intro x hx
    rw [pareto_mixture_tail_nonnegative q a S x hq.le hq1 ha haS hx,hqa]
  · change mean ν-0=t*spProfit ν 0
    rw [hmean,sub_zero,pareto_mixture_profit q a S hq.le hq1 ha haS,hqa,mul_inv_cancel₀ ht.ne']
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem threshold_low_pos (M S : ℝ) (hM : 0<M) (hS : 1<S) : 0<deltaL M S := by
  have hsc : 1 < sc M S := by unfold sc;apply (lt_div_iff₀ hM).mpr;linarith
  have hl : 0<Real.log (sc M S) := Real.log_pos hsc
  have he : 0<Real.exp 1:=Real.exp_pos _
  have hs0 : 0<sc M S:=lt_trans zero_lt_one hsc
  have hxlo : -1/Real.exp 1≤ -1/(Real.exp 1*sc M S) := by
    apply (div_le_div_iff₀ he (mul_pos he hs0)).mpr
    nlinarith
  have hx0 : -1/(Real.exp 1*sc M S)<0:=div_neg_of_neg_of_pos (by norm_num) (mul_pos he hs0)
  have hw:=(lambert_spec _ hxlo hx0).1
  unfold deltaL
  exact div_pos_of_neg_of_neg (by nlinarith [mul_pos hM hl]) (by linarith)

theorem transport_profit_bound (ν : Measure ℝ) (c B : ℝ) (hm : Market ν c)
    (hc : c< mean ν) (h : ppProfit (standardize ν c) 0≤B*spProfit (standardize ν c) 0) :
    ppProfit ν c≤B*spProfit ν c := by
  rw [standardized_pp ν c hm hc,standardized_sp ν c hm hc]
  calc
    _≤(mean ν-c)*(B*spProfit (standardize ν c) 0) :=
      mul_le_mul_of_nonneg_left h (sub_pos.mpr hc).le
    _=B*((mean ν-c)*spProfit (standardize ν c) 0) := by ring

theorem general_low_bound (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c< mean ν) :
    ppProfit ν c≤lowBound (margin ν c) (coefDev ν)*spProfit ν c := by
  apply transport_profit_bound ν c _ hm hc
  have h:=low_distribution_bound (standardize ν c) (standardized_market ν c hm hc)
    (standardized_mean ν c hm hc)
  rw [standardized_deviation ν c hm hc] at h
  have he : lambertWm1 ((coefDev ν/margin ν c-1)/Real.exp 1)/(coefDev ν/margin ν c-1)=
      lowBound (margin ν c) (coefDev ν) := by
    unfold lowBound
    rw [show coefDev ν/margin ν c-1= -(1-coefDev ν/margin ν c) by ring,div_neg,neg_div]
    ring
  rw [he] at h
  exact h

theorem general_medium_bound (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c)
    (hc : c< mean ν) (hS : IsScale ν S) (hD : 0<coefDev ν) :
    ppProfit ν c≤ medBound (margin ν c) S (coefDev ν)*spProfit ν c := by
  apply transport_profit_bound ν c _ hm hc
  have hM:=market_margin_pos ν c hm hc
  have hmean:=standardized_mean ν c hm hc
  have h:=medium_distribution_bound (standardize ν c) (sc (margin ν c) S)
    (standardized_market ν c hm hc) hmean (standardized_scale ν c hm hc S hS)
  rw [standardized_deviation ν c hm hc] at h
  have hb : ppProfit (standardize ν c) 0≤
      (Real.log (sc (margin ν c) S)/(coefDev ν/margin ν c))*spProfit (standardize ν c) 0 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (div_pos hD hM)).mpr
    simpa only [mul_comm] using h
  have he : Real.log (sc (margin ν c) S)/(coefDev ν/margin ν c)=medBound (margin ν c) S (coefDev ν) := by
    unfold medBound
    field_simp
  rw [he] at hb
  exact hb

theorem general_high_bound (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c)
    (hc : c< mean ν) (hS : IsScale ν S) (hS1 : 1<S)
    (hD : deltaM (margin ν c) S≤coefDev ν) :
    ppProfit ν c≤highBound (margin ν c) S (coefDev ν)*spProfit ν c := by
  apply transport_profit_bound ν c _ hm hc
  have hM:=market_margin_pos ν c hm hc
  have hsc : 1 < sc (margin ν c) S := by unfold sc;apply (lt_div_iff₀ hM).mpr;linarith
  have hden : S+margin ν c-1≠0 := by linarith
  have hr:=threshold_rescaling (margin ν c) S hM.ne' hden
  have hd : deltaM 1 (sc (margin ν c) S)≤coefDev (standardize ν c) := by
    rw [standardized_deviation ν c hm hc]
    apply (le_div_iff₀ hM).mpr
    rw [hr.2.1] at hD
    simpa only [mul_comm] using hD
  have h:=high_distribution_bound_closed (standardize ν c) (sc (margin ν c) S)
    (standardized_market ν c hm hc) (standardized_mean ν c hm hc)
    (standardized_scale ν c hm hc S hS) hsc hd
  rw [standardized_deviation ν c hm hc] at h
  exact h

theorem all_regime_upper_bounds (ν : Measure ℝ) (c : ℝ) (hm : Market ν c)
    (hc : c< mean ν) :
    (∀ S : ℝ,1<S→IsScale ν S→
      (coefDev ν≤deltaL (margin ν c) S→ppProfit ν c≤lowBound (margin ν c) (coefDev ν)*spProfit ν c) ∧
      (deltaL (margin ν c) S≤coefDev ν→coefDev ν≤deltaM (margin ν c) S→
        ppProfit ν c≤ medBound (margin ν c) S (coefDev ν)*spProfit ν c) ∧
      (deltaM (margin ν c) S≤coefDev ν→coefDev ν≤deltaH (margin ν c) S→
        ppProfit ν c≤highBound (margin ν c) S (coefDev ν)*spProfit ν c)) ∧
    (Unbounded ν→ppProfit ν c≤lowBound (margin ν c) (coefDev ν)*spProfit ν c) := by
  constructor
  · intro S hS1 hS
    refine ⟨fun _=>general_low_bound ν c hm hc,?_,fun hd _=>general_high_bound ν c S hm hc hS hS1 hd⟩
    intro hd _
    exact general_medium_bound ν c S hm hc hS ((threshold_low_pos _ S (market_margin_pos ν c hm hc) hS1).trans_le hd)
  · intro _
    exact general_low_bound ν c hm hc
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set Filter
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem low_mixture_endpoint_atom (q a B : ℝ) (hq : 0<q) (hq1 : q≤1)
    (ha : 0<a) (ha1 : a≤1) (hB : 1<B) :
    (lowMixture q a B).real {B}=q*a/B ∧ 0<(lowMixture q a B) {B} := by
  let ν:=lowMixture q a B
  letI:=low_mixture_probability q a B hq.le hq1 ha
  have he : ν {B}=ν (Ici B) := by
    apply measure_congr
    filter_upwards [low_mixture_bounds q a B ha ha1 hB.le] with v hv
    apply propext
    change (v=B ↔ B≤v)
    exact ⟨fun h=>h.ge,fun h=>le_antisymm hv.2 h⟩
  have ht : tail ν B=q*a/B := by
    rw [low_mixture_tail_formula q a B B hq.le hq1 ha ha1 hB.le]
    simp [not_le.mpr (ha1.trans_lt hB),not_le.mpr hB]
  have hr : ν.real {B}=q*a/B := by rw [measureReal_def,he];exact ht
  refine ⟨hr,?_⟩
  have hp : 0<ν.real {B}:=by rw [hr];exact div_pos (mul_pos hq ha) (zero_lt_one.trans hB)
  exact ENNReal.toReal_pos_iff.mp hp |>.1

theorem low_mixture_scale_of_mean (q a B : ℝ) (hq : 0<q) (hq1 : q≤1)
    (ha : 0<a) (ha1 : a≤1) (hB : 1<B) (hm : mean (lowMixture q a B)=1) :
    IsScale (lowMixture q a B) B := by
  rw [IsScale,hm,mul_one]
  constructor
  · apply measure_eq_zero_iff_ae_notMem.mpr
    exact (low_mixture_bounds q a B ha ha1 hB.le).mono (fun _ h=>not_lt.mpr h.2)
  · intro k hk
    exact (low_mixture_endpoint_atom q a B hq hq1 ha ha1 hB).2.trans_le
      (measure_mono (singleton_subset_iff.mpr hk))

theorem low_mixture_deviation (q a B : ℝ) (hq : 0<q) (hq1 : q≤1)
    (ha : 0<a) (ha1 : a≤1) (hB : 1<B) (hm : mean (lowMixture q a B)=1) :
    coefDev (lowMixture q a B)=q*a*Real.log B := by
  rw [normalized_upper_integral _ 0 B (low_mixture_market q a B hq.le hq1 ha ha1 hB.le) hm
    (low_mixture_scale_of_mean q a B hq hq1 ha ha1 hB hm)]
  calc
    _ = ∫p in (1:ℝ)..B,q*a/p := by
      apply intervalIntegral.integral_congr_Ioo_of_le hB.le
      intro p hp
      rw [low_mixture_tail_formula q a B p hq.le hq1 ha ha1 hB.le,
        if_neg (not_le.mpr (ha1.trans_lt hp.1)),if_neg (not_le.mpr hp.1),if_pos hp.2.le]
    _ = q*a*Real.log B := by rw [reciprocal_price_integral _ _ _ zero_lt_one (zero_lt_one.trans hB),div_one]
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

theorem continuous_boundary_statistics :
    let ν:=paretoMixture (1/2) 1 (Real.exp 1)
    mean ν=1 ∧ coefDev ν=1/2 ∧ IsScale ν (Real.exp 1) ∧ spProfit ν 0=1/2 := by
  dsimp only
  have he : 1<Real.exp 1:=by simpa using Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)
  have hm : (1/2:ℝ)*1*(1+Real.log (Real.exp 1/1))=1 := by norm_num
  have hmean : mean (paretoMixture (1/2) 1 (Real.exp 1))=1 := by
    rw [pareto_mixture_mean (1/2) 1 (Real.exp 1) (by norm_num) (by norm_num) (by norm_num) he.le]
    exact hm
  refine ⟨hmean,?_,pareto_mixture_scale_of_mean (1/2) 1 (Real.exp 1) (by norm_num) (by norm_num) (by norm_num) he.le hmean,?_⟩
  · rw [pareto_mixture_deviation_above (1/2) 1 (Real.exp 1) (by norm_num) (by norm_num) le_rfl he.le hm]
    norm_num
  · rw [pareto_mixture_profit (1/2) 1 (Real.exp 1) (by norm_num) (by norm_num) (by norm_num) he.le]
    norm_num

theorem collapsed_interval_statistics :
    let ν:=paretoMixture (1/2) 2 2
    mean ν=1 ∧ coefDev ν=1/2 ∧ IsScale ν 2 ∧ spProfit ν 0=1 := by
  dsimp only
  have hm : (1/2:ℝ)*2*(1+Real.log ((2:ℝ)/2))=1 := by norm_num
  have hmean : mean (paretoMixture (1/2) 2 2)=1 := by
    rw [pareto_mixture_mean (1/2) 2 2 (by norm_num) (by norm_num) (by norm_num) le_rfl]
    exact hm
  refine ⟨hmean,?_,pareto_mixture_scale_of_mean (1/2) 2 2 (by norm_num) (by norm_num) (by norm_num) le_rfl hmean,?_⟩
  · rw [pareto_mixture_deviation_above (1/2) 2 2 (by norm_num) (by norm_num) (by norm_num) le_rfl hm]
    norm_num
  · rw [pareto_mixture_profit (1/2) 2 2 (by norm_num) (by norm_num) (by norm_num) le_rfl]
    norm_num

theorem upper_endpoint_retained :
    tail (paretoMixture (1/2) 2 2) 2=1/2 ∧ tail (paretoMixture (1/2) 2 2) 3=0 := by
  constructor
  · rw [pareto_mixture_tail_nonnegative (1/2) 2 2 2 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)]
    norm_num
  · rw [pareto_mixture_tail_nonnegative (1/2) 2 2 3 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)]
    norm_num

theorem zero_endpoint_retained :
    tail (paretoMixture (1/2) 2 2) 0=1 ∧ tail (paretoMixture (1/2) 2 2) 1=1/2 := by
  constructor
  · rw [pareto_mixture_tail_nonnegative (1/2) 2 2 0 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)]
    norm_num
  · rw [pareto_mixture_tail_nonnegative (1/2) 2 2 1 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)]
    norm_num
end Queelius.PersonalizedPricing.Controls

end

section
theorem original_high_tightness : (
∀ (S : Real),
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S →
    ∀ (D : Real),
      @Membership.mem Real (Set Real) (@Set.instMembership Real)
          (@Set.Icc Real Real.instPreorder
            (ValuePersPricing.Deviation.deltaM (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S)
            (ValuePersPricing.Deviation.deltaH (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S))
          D →
        @Exists (@MeasureTheory.Measure Real Real.measurableSpace)
          fun (ν : @MeasureTheory.Measure Real Real.measurableSpace) =>
          And (ValuePersPricing.Deviation.Market ν (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
            (And
              (@Eq Real (ValuePersPricing.Deviation.mean ν)
                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
              (And (ValuePersPricing.Deviation.IsScale ν S)
                (And (@Eq Real (ValuePersPricing.Deviation.coefDev ν) D)
                  (And
                    (∀ (x : Real),
                      @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) x →
                        @Eq Real (ValuePersPricing.Deviation.tail ν x)
                          (@ite Real (@Eq Real x (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
                            (Real.decidableEq x (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                            (@ite Real
                              (@LE.le Real Real.instLE x
                                (@HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@Inv.inv Real Real.instInv
                                    (@Neg.neg Real Real.instNeg
                                      (ValuePersPricing.Deviation.lambertWm1
                                        (@HDiv.hDiv Real Real Real
                                          (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                          (@Neg.neg Real Real.instNeg
                                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                              (Real.exp
                                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                              S)
                                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))))))
                                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D)))
                              (Real.decidableLE x
                                (@HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@Inv.inv Real Real.instInv
                                    (@Neg.neg Real Real.instNeg
                                      (ValuePersPricing.Deviation.lambertWm1
                                        (@HDiv.hDiv Real Real Real
                                          (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                          (@Neg.neg Real Real.instNeg
                                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                              (Real.exp
                                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                              S)
                                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))))))
                                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D)))
                              (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D)
                              (@ite Real (@LE.le Real Real.instLE x S) (Real.decidableLE x S)
                                (@HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@Inv.inv Real Real.instInv
                                    (@Neg.neg Real Real.instNeg
                                      (ValuePersPricing.Deviation.lambertWm1
                                        (@HDiv.hDiv Real Real Real
                                          (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                          (@Neg.neg Real Real.instNeg
                                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                              (Real.exp
                                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                              S)
                                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D))))))
                                  x)
                                (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))))))
                    (@Eq Real
                      (ValuePersPricing.Deviation.ppProfit ν
                        (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
                      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                        (@Neg.neg Real Real.instNeg
                          (ValuePersPricing.Deviation.lambertWm1
                            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                              (@Neg.neg Real Real.instNeg
                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                              (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                  (Real.exp (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) S)
                                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) D)))))
                        (ValuePersPricing.Deviation.spProfit ν
                          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))))))))
) := by
  intro S hS D hD
  exact Queelius.PersonalizedPricing.high_tight_law S D hS hD

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem medium_tight_law (S D : ℝ) (hS : 1<S) (hD : D∈Icc (deltaL 1 S) (deltaM 1 S)) :
    ∃ν:Measure ℝ,Market ν 0 ∧ mean ν=1 ∧ IsScale ν S ∧ coefDev ν=D ∧
      (∀x:ℝ,0≤x → tail ν x=
        if x=0 then 1 else if x<Real.exp 1*S^(1-1/D) then D/Real.log S/Real.exp 1*S^(1/D-1)
        else if x≤S then D/Real.log S/x else 0) ∧
      coefDev ν*ppProfit ν 0=Real.log S*spProfit ν 0 := by
  let t:=Real.log S/D
  let a:=Real.exp (1+Real.log S-t)
  let q:=(t*a)⁻¹
  obtain ⟨hd,ha,ha1,hq,hq1,hqa,he,hae,hqe⟩:=medium_tight_parameters S D hS hD
  change 0<a at ha
  change a≤1 at ha1
  change 0<q at hq
  change q≤1 at hq1
  change q*a=D/Real.log S at hqa
  change q*a*(1+Real.log (S/a))=1 at he
  change a=Real.exp 1*S^(1-1/D) at hae
  change q=D/Real.log S/Real.exp 1*S^(1/D-1) at hqe
  have haS:=ha1.trans hS.le
  let ν:=paretoMixture q a S
  have hm:=pareto_mixture_market q a S hq.le hq1 ha haS
  have hmean : mean ν=1:=(pareto_mixture_mean q a S hq.le hq1 ha haS).trans he
  have hscale:=pareto_mixture_scale_of_mean q a S hq hq1 ha haS hmean
  have hdev : coefDev ν=D := by
    rw [pareto_mixture_deviation_below q a S hq hq1 ha ha1 hS he,hqa]
    exact div_mul_cancel₀ D (Real.log_pos hS).ne'
  refine ⟨ν,hm,hmean,hscale,hdev,?_,?_⟩
  · intro x hx
    rw [pareto_mixture_tail_nonnegative q a S x hq.le hq1 ha haS hx,hqa,←hae,←hqe]
    by_cases hx0:x=0
    · simp [hx0]
    · simp only [if_neg hx0]
      by_cases hxa:x<a
      · simp [hxa,hxa.le]
      · by_cases hxae:x≤a
        · have heq:x=a:=le_antisymm hxae (le_of_not_gt hxa)
          subst x
          simp only [le_refl,if_true,lt_self_iff_false,if_false,haS]
          exact (eq_div_iff ha.ne').mpr hqa
        · simp [hxa,hxae]
  · change coefDev ν*(mean ν-0)=Real.log S*spProfit ν 0
    rw [hdev,hmean,sub_zero,mul_one,pareto_mixture_profit q a S hq.le hq1 ha haS,hqa]
    field_simp [(Real.log_pos hS).ne']
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

noncomputable def twoPoint : Measure ℝ :=
  (ENNReal.ofReal (1/2 : ℝ)) • Measure.dirac 0 + (ENNReal.ofReal (1/2 : ℝ)) • Measure.dirac 2

theorem two_point_market : Market twoPoint 0 := by
  have hp : IsProbabilityMeasure twoPoint := by
    constructor
    norm_num [twoPoint]
    rw [←ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hp,by norm_num,?_,?_⟩
  · simp [twoPoint,ae_add_measure_iff]
  · apply Integrable.add_measure
    · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac (by simp)).smul_measure (by norm_num)

theorem two_point_mean : mean twoPoint=1 := by
  unfold mean twoPoint
  rw [integral_add_measure]
  · norm_num
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)

theorem two_point_deviation : coefDev twoPoint=1/2 := by
  rw [coefDev,two_point_mean]
  unfold twoPoint
  rw [integral_add_measure]
  · norm_num
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)

theorem two_point_scale : IsScale twoPoint 2 := by
  rw [IsScale,two_point_mean,mul_one]
  constructor
  · norm_num [twoPoint,Measure.dirac_apply',measurableSet_Ioi]
  · intro k hk
    have h : 0<(ENNReal.ofReal (1/2 : ℝ)) * Measure.dirac (2:ℝ) (Ioi k) := by
      norm_num [Measure.dirac_apply',measurableSet_Ioi,hk]
    unfold twoPoint
    rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
    exact h.trans_le (le_add_left le_rfl)

theorem two_point_profit : spProfit twoPoint 0=1 := by
  apply le_antisymm
  · simpa only [two_point_mean,sub_zero] using sp_le_surplus twoPoint 0 two_point_market
  · have h:=price_le_sp twoPoint 0 two_point_market 2
    have ht : tail twoPoint 2=1/2 := by
      norm_num [tail,twoPoint,Measure.dirac_apply',measurableSet_Ici,ENNReal.toReal_add]
    rw [ht] at h
    norm_num at h ⊢
    exact h

theorem two_point_high_endpoint_sharp :
    coefDev twoPoint=deltaH 1 2 ∧
    ppProfit twoPoint 0=highBound 1 2 (coefDev twoPoint)*spProfit twoPoint 0 := by
  rw [two_point_deviation,two_point_profit]
  norm_num [deltaH,highBound,sc,ppProfit,two_point_mean]
  rw [show Real.exp 1*2*(1/2)=Real.exp 1 by ring]
  rw [lambert_boundary]
  norm_num

theorem threshold_scale_one : deltaL 1 1=0 ∧ deltaM 1 1=0 ∧ deltaH 1 1=0 := by
  norm_num [deltaL,deltaM,deltaH,sc]

theorem high_scalar_boundary : -lambertWm1 (-1/Real.exp 1)=1 := by rw [lambert_boundary];norm_num
end Queelius.PersonalizedPricing.Controls

end

section
open MeasureTheory Set Filter Topology
namespace ValuePersPricing.Deviation

/-- Lemma EC.1 (p. ec3), Eq. (EC.7): for `c = 0`, `µ = 1`, a law of scale `S` and `D > δ_M`,
`R_PP/R_SP ≤ −W₋₁(−1/(e S (1 − D)))`, stated multiplicatively. -/
theorem lemma_EC_1 (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0) (hμ : mean ν = 1)
    (hS : IsScale ν S) (hD : deltaM 1 S < coefDev ν) :
    ppProfit ν 0 ≤
      -lambertWm1 (-1 / (Real.exp 1 * S * (1 - coefDev ν))) * spProfit ν 0 := Queelius.PersonalizedPricing.high_distribution_bound ν S hm hμ hS hD

end ValuePersPricing.Deviation

namespace ValuePersPricing.Deviation

/-- Lemma 2 (p. 13): for a law of scale `S` and margin `M`, `0 ≤ D ≤ δ_H` and
`0 ≤ δ_L ≤ δ_M ≤ δ_H`. -/
theorem lemma_2 (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c) (hc : c < mean ν)
    (hS : IsScale ν S) :
    0 ≤ coefDev ν ∧ coefDev ν ≤ deltaH (margin ν c) S ∧
    0 ≤ deltaL (margin ν c) S ∧ deltaL (margin ν c) S ≤ deltaM (margin ν c) S ∧
    deltaM (margin ν c) S ≤ deltaH (margin ν c) S := Queelius.PersonalizedPricing.full_deviation_partition ν c S hm hc hS

end ValuePersPricing.Deviation

end

section
theorem root_upper_clause : (
  ∀ (ν : @MeasureTheory.Measure Real Real.measurableSpace) (c : Real),
    ValuePersPricing.Deviation.Market ν c →
      @LT.lt Real Real.instLT c (ValuePersPricing.Deviation.mean ν) →
        And
          (∀ (S : Real),
            @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S →
              ValuePersPricing.Deviation.IsScale ν S →
                And
                  (@LE.le Real Real.instLE (ValuePersPricing.Deviation.coefDev ν)
                      (ValuePersPricing.Deviation.deltaL (ValuePersPricing.Deviation.margin ν c) S) →
                    @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                        (ValuePersPricing.Deviation.lowBound (ValuePersPricing.Deviation.margin ν c)
                          (ValuePersPricing.Deviation.coefDev ν))
                        (ValuePersPricing.Deviation.spProfit ν c)))
                  (And
                    (@LE.le Real Real.instLE (ValuePersPricing.Deviation.deltaL (ValuePersPricing.Deviation.margin ν c) S)
                        (ValuePersPricing.Deviation.coefDev ν) →
                      @LE.le Real Real.instLE (ValuePersPricing.Deviation.coefDev ν)
                          (ValuePersPricing.Deviation.deltaM (ValuePersPricing.Deviation.margin ν c) S) →
                        @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                            (ValuePersPricing.Deviation.medBound (ValuePersPricing.Deviation.margin ν c) S
                              (ValuePersPricing.Deviation.coefDev ν))
                            (ValuePersPricing.Deviation.spProfit ν c)))
                    (@LE.le Real Real.instLE (ValuePersPricing.Deviation.deltaM (ValuePersPricing.Deviation.margin ν c) S)
                        (ValuePersPricing.Deviation.coefDev ν) →
                      @LE.le Real Real.instLE (ValuePersPricing.Deviation.coefDev ν)
                          (ValuePersPricing.Deviation.deltaH (ValuePersPricing.Deviation.margin ν c) S) →
                        @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                            (ValuePersPricing.Deviation.highBound (ValuePersPricing.Deviation.margin ν c) S
                              (ValuePersPricing.Deviation.coefDev ν))
                            (ValuePersPricing.Deviation.spProfit ν c)))))
          (ValuePersPricing.Deviation.Unbounded ν →
            @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
              (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                (ValuePersPricing.Deviation.lowBound (ValuePersPricing.Deviation.margin ν c)
                  (ValuePersPricing.Deviation.coefDev ν))
                (ValuePersPricing.Deviation.spProfit ν c)))
) := fun ν c hm hc => Queelius.PersonalizedPricing.all_regime_upper_bounds ν c hm hc

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem low_tight_law (S D : ℝ) (hS : 1<S) (hD : D∈Ioc 0 (deltaL 1 S)) :
    ∃ν:Measure ℝ,Market ν 0 ∧ mean ν=1 ∧ IsScale ν S ∧ coefDev ν=D ∧
      (∀x:ℝ,0≤x → tail ν x=
        if x<(lambertWm1 ((D-1)/Real.exp 1)/(D-1))⁻¹ then 1
        else if x≤1 then (lambertWm1 ((D-1)/Real.exp 1)/(D-1))⁻¹/x
        else if x≤S then D/(Real.log S*x) else 0) ∧
      ppProfit ν 0=lambertWm1 ((D-1)/Real.exp 1)/(D-1)*spProfit ν 0 := by
  let a:=(lambertWm1 ((D-1)/Real.exp 1)/(D-1))⁻¹
  let b:=D/Real.log S
  let q:=b/a
  obtain ⟨ha,ha1,hb,hba,he⟩:=low_tight_parameters S D hS hD
  change 0<a at ha
  change a≤1 at ha1
  change 0<b at hb
  change b≤a at hba
  change a*(1-Real.log a)+D=1 at he
  have hq : 0<q:=div_pos hb ha
  have hq1 : q≤1:=(div_le_one ha).mpr hba
  have hqa : q*a=b:=div_mul_cancel₀ b ha.ne'
  have hlog : q*a*Real.log S=D := by rw [hqa];exact div_mul_cancel₀ D (Real.log_pos hS).ne'
  let ν:=lowMixture q a S
  have hm:=low_mixture_market q a S hq.le hq1 ha ha1 hS.le
  have hmean : mean ν=1 := by
    rw [low_mixture_mean q a S hq.le hq1 ha ha1 hS.le,hlog]
    exact he
  have hscale:=low_mixture_scale_of_mean q a S hq hq1 ha ha1 hS hmean
  have hdev : coefDev ν=D:=(low_mixture_deviation q a S hq hq1 ha ha1 hS hmean).trans hlog
  refine ⟨ν,hm,hmean,hscale,hdev,?_,?_⟩
  · intro x hx
    change tail ν x=if x<a then 1 else if x≤1 then a/x else if x≤S then D/(Real.log S*x) else 0
    rw [low_mixture_tail_formula q a S x hq.le hq1 ha ha1 hS.le,hqa]
    have hbx : b/x=D/(Real.log S*x):=by dsimp [b];ring
    rw [hbx]
    by_cases hlt:x<a
    · simp [hlt,hlt.le]
    · by_cases hle:x≤a
      · have heq:x=a:=le_antisymm hle (le_of_not_gt hlt)
        subst x;simp [ha.ne',ha1]
      · simp [hlt,hle]
  · change mean ν-0=lambertWm1 ((D-1)/Real.exp 1)/(D-1)*spProfit ν 0
    rw [hmean,sub_zero,low_mixture_profit q a S hq.le hq1 ha ha1 hS.le]
    have hr : lambertWm1 ((D-1)/Real.exp 1)/(D-1)≠0:=by
      intro hz
      have he0 : a=0 := by
        change (lambertWm1 ((D-1)/Real.exp 1)/(D-1))⁻¹=0
        rw [hz,inv_zero]
      exact ha.ne' he0
    exact (mul_inv_cancel₀ hr).symm
end Queelius.PersonalizedPricing

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

theorem translated_two_point_statistics :
    Market (affineLaw twoPoint 3 1) 1 ∧ mean (affineLaw twoPoint 3 1)=3 ∧
    IsScale (affineLaw twoPoint 3 1) (5/3) ∧ coefDev (affineLaw twoPoint 3 1)=1/3 ∧
    spProfit (affineLaw twoPoint 3 1) 1=2 ∧ ppProfit (affineLaw twoPoint 3 1) 1=2 := by
  have hs : IsScale twoPoint (sc (1-1/3) (5/3)) := by
    convert two_point_scale using 1 <;> norm_num [sc]
  refine ⟨affine_market twoPoint 3 1 two_point_market (by norm_num) (by norm_num),
    affine_mean twoPoint 3 1 two_point_market two_point_mean,
    affine_scale twoPoint 3 1 (5/3) two_point_market two_point_mean (by norm_num) (by norm_num) hs,?_,?_,?_⟩
  · rw [affine_deviation twoPoint 3 1 two_point_market two_point_mean (by norm_num) (by norm_num),two_point_deviation]
    norm_num
  · rw [affine_sp twoPoint 3 1 two_point_market two_point_mean (by norm_num) (by norm_num),two_point_profit]
    norm_num
  · norm_num [ppProfit,affine_mean twoPoint 3 1 two_point_market two_point_mean]

theorem translated_lower_atom_included : tail (affineLaw twoPoint 3 1) 1=1 := by
  have h:=affine_tail twoPoint 3 1 0 two_point_market two_point_mean (by norm_num)
  norm_num [tail,twoPoint,Measure.dirac_apply',measurableSet_Ici,ENNReal.toReal_add] at h ⊢
  exact h

theorem translated_upper_atom_included : tail (affineLaw twoPoint 3 1) 5=1/2 := by
  have h:=affine_tail twoPoint 3 1 2 two_point_market two_point_mean (by norm_num)
  norm_num [tail,twoPoint,Measure.dirac_apply',measurableSet_Ici,ENNReal.toReal_add] at h ⊢
  exact h

theorem translated_above_support_zero : tail (affineLaw twoPoint 3 1) 7=0 := by
  have h:=affine_tail twoPoint 3 1 3 two_point_market two_point_mean (by norm_num)
  norm_num [tail,twoPoint,Measure.dirac_apply',measurableSet_Ici,ENNReal.toReal_add] at h ⊢
  exact h
end Queelius.PersonalizedPricing.Controls

end

section
noncomputable section
open Set MeasureTheory
namespace Queelius.PersonalizedPricing.Controls
open ValuePersPricing.Deviation

theorem medium_upper_cutoff (S:ℝ) (hS:1<S) :
    Real.exp (1+Real.log S-Real.log S/deltaM 1 S)=1 := by
  have hl : Real.log S≠0:=(Real.log_pos hS).ne'
  have he : 1+Real.log S-Real.log S/deltaM 1 S=0 := by
    simp only [deltaM,sc_one,one_mul]
    field_simp
    <;> ring
  rw [he,Real.exp_zero]

theorem low_cutoff_included : tail (lowMixture (1/2) (1/2) 4) (1/2)=1 := by
  rw [low_mixture_tail_formula (1/2) (1/2) 4 (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem low_atom_at_one_control :
    tail (lowMixture (1/2) (1/2) 4) 1=1/2 ∧
    tail (lowMixture (1/2) (1/2) 4) (3/2)=1/6 := by
  constructor <;> rw [low_mixture_tail_formula (1/2) (1/2) 4 _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)] <;> norm_num

theorem low_upper_endpoint_included :
    tail (lowMixture (1/2) (1/2) 4) 4=1/16 ∧
    tail (lowMixture (1/2) (1/2) 4) 5=0 := by
  constructor <;> rw [low_mixture_tail_formula (1/2) (1/2) 4 _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)] <;> norm_num

theorem zero_weight_loses_upper_tail : tail (lowMixture 0 (1/2) 4) 2=0 := by
  rw [low_mixture_tail_formula 0 (1/2) 4 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num
end Queelius.PersonalizedPricing.Controls

end

section
open MeasureTheory Set Filter Topology
namespace ValuePersPricing.Deviation

/-- Lemma EC.3 (p. ec7): tight distributions for `c = 0`, `µ = 1`, `S > 1` (δ's at `M = 1`).
Each part gives a law with the stated cCDF on `x ≥ 0`, scale `S`, coefficient of deviation `D`
and mean `1` that attains (EC.5), (EC.6), (EC.7) respectively with equality.
Corrected: (a) for `D ∈ (0, δ_L]` (at `D = 0` the printed law is the point mass at 1, of scale 1);
(c) the third piece of `F̄_H` is on `(α_H/(1 − D), S]` (the printed `F̄_H(S) = 0` is not
left-continuous, so no law has it). -/
theorem lemma_EC_3 (S : ℝ) (hS : 1 < S) :
    (∀ D ∈ Ioc 0 (deltaL 1 S),
      ∃ ν : Measure ℝ, Market ν 0 ∧ mean ν = 1 ∧ IsScale ν S ∧ coefDev ν = D ∧
        (∀ x : ℝ, 0 ≤ x → tail ν x =
          if x < (lambertWm1 ((D - 1) / Real.exp 1) / (D - 1))⁻¹ then 1
          else if x ≤ 1 then (lambertWm1 ((D - 1) / Real.exp 1) / (D - 1))⁻¹ / x
          else if x ≤ S then D / (Real.log S * x)
          else 0) ∧
        ppProfit ν 0 =
          lambertWm1 ((D - 1) / Real.exp 1) / (D - 1) * spProfit ν 0) ∧
    (∀ D ∈ Icc (deltaL 1 S) (deltaM 1 S),
      ∃ ν : Measure ℝ, Market ν 0 ∧ mean ν = 1 ∧ IsScale ν S ∧ coefDev ν = D ∧
        (∀ x : ℝ, 0 ≤ x → tail ν x =
          if x = 0 then 1
          else if x < Real.exp 1 * S ^ (1 - 1 / D) then
            D / Real.log S / Real.exp 1 * S ^ (1 / D - 1)
          else if x ≤ S then D / Real.log S / x
          else 0) ∧
        coefDev ν * ppProfit ν 0 = Real.log S * spProfit ν 0) ∧
    (∀ D ∈ Icc (deltaM 1 S) (deltaH 1 S),
      ∃ ν : Measure ℝ, Market ν 0 ∧ mean ν = 1 ∧ IsScale ν S ∧ coefDev ν = D ∧
        (∀ x : ℝ, 0 ≤ x → tail ν x =
          if x = 0 then 1
          else if x ≤ (-lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))))⁻¹ / (1 - D) then 1 - D
          else if x ≤ S then (-lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))))⁻¹ / x
          else 0) ∧
        ppProfit ν 0 =
          -lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))) * spProfit ν 0) := by
  exact ⟨fun D hD=>Queelius.PersonalizedPricing.low_tight_law S D hS hD,
    fun D hD=>Queelius.PersonalizedPricing.medium_tight_law S D hS hD,
    fun D hD=>Queelius.PersonalizedPricing.high_tight_law S D hS hD⟩

end ValuePersPricing.Deviation

end

section
noncomputable section
open MeasureTheory Set
namespace Queelius.PersonalizedPricing
open ValuePersPricing.Deviation

theorem affine_profit_equality (ν : Measure ℝ) (μ c B : ℝ) (hm : Market ν 0)
    (hmean : mean ν=1) (hc : 0 ≤ c) (hμ : c < μ)
    (he : ppProfit ν 0=B*spProfit ν 0) :
    ppProfit (affineLaw ν μ c) c=B*spProfit (affineLaw ν μ c) c := by
  rw [affine_pp ν μ c hm hmean,affine_sp ν μ c hm hmean hc hμ,he]
  ring

theorem lift_normalized_attainer (μ c S D B : ℝ) (hc : 0 ≤ c) (hμ : c < μ)
    (h : ∃ν : Measure ℝ, Market ν 0 ∧ mean ν=1 ∧ IsScale ν (sc (1-c/μ) S) ∧
      coefDev ν=D/(1-c/μ) ∧ ppProfit ν 0=B*spProfit ν 0) :
    ∃ρ : Measure ℝ,Market ρ c ∧ mean ρ=μ ∧ IsScale ρ S ∧ coefDev ρ=D ∧
      ppProfit ρ c=B*spProfit ρ c := by
  obtain ⟨ν,hm,hmean,hscale,hdev,hprofit⟩:=h
  have hM : 0 < 1-c/μ := sub_pos.mpr ((div_lt_one (lt_of_le_of_lt hc hμ)).mpr hμ)
  refine ⟨affineLaw ν μ c,affine_market ν μ c hm hc hμ,affine_mean ν μ c hm hmean,
    affine_scale ν μ c S hm hmean hc hμ hscale,?_,affine_profit_equality ν μ c B hm hmean hc hμ hprofit⟩
  rw [affine_deviation ν μ c hm hmean hc hμ,hdev]
  field_simp [hM.ne']

theorem general_tightness (μ c S D : ℝ) (hc : 0 ≤ c) (hμ : c < μ) (hS : 1 < S)
    (hD : 0 < D) :
    (D ≤ deltaL (1-c/μ) S →
      ∃ν : Measure ℝ,Market ν c ∧ mean ν=μ ∧ IsScale ν S ∧ coefDev ν=D ∧
        ppProfit ν c=lowBound (1-c/μ) D*spProfit ν c) ∧
    (deltaL (1-c/μ) S ≤ D → D ≤ deltaM (1-c/μ) S →
      ∃ν : Measure ℝ,Market ν c ∧ mean ν=μ ∧ IsScale ν S ∧ coefDev ν=D ∧
        ppProfit ν c=medBound (1-c/μ) S D*spProfit ν c) ∧
    (deltaM (1-c/μ) S ≤ D → D ≤ deltaH (1-c/μ) S →
      ∃ν : Measure ℝ,Market ν c ∧ mean ν=μ ∧ IsScale ν S ∧ coefDev ν=D ∧
        ppProfit ν c=highBound (1-c/μ) S D*spProfit ν c) := by
  let M:=1-c/μ
  have hM : 0 < M := sub_pos.mpr ((div_lt_one (lt_of_le_of_lt hc hμ)).mpr hμ)
  have hsc : 1 < sc M S := by unfold sc;apply (lt_div_iff₀ hM).mpr;linarith
  have hden : S+M-1 ≠ 0 := by linarith
  have hr:=threshold_rescaling M S hM.ne' hden
  have ht:=lemma_EC_3 (sc M S) hsc
  have hDN : 0 < D/M:=div_pos hD hM
  constructor
  · intro hlow
    have hd : D/M ≤ deltaL 1 (sc M S) := by
      apply (div_le_iff₀ hM).mpr
      change D ≤ deltaL M S at hlow
      rw [hr.1] at hlow
      simpa only [mul_comm] using hlow
    obtain ⟨ν,hm,hmean,hscale,hdev,_,hp⟩:=ht.1 (D/M) ⟨hDN,hd⟩
    apply lift_normalized_attainer μ c S D _ hc hμ
    refine ⟨ν,hm,hmean,hscale,hdev,?_⟩
    have he : lambertWm1 ((D/M-1)/Real.exp 1)/(D/M-1)=lowBound M D := by
      unfold lowBound
      rw [show D/M-1= -(1-D/M) by ring,div_neg,neg_div]
      ring
    rw [he] at hp
    exact hp
  constructor
  · intro hlo hhi
    have hdlo : deltaL 1 (sc M S) ≤ D/M := by
      apply (le_div_iff₀ hM).mpr
      change deltaL M S ≤ D at hlo
      rw [hr.1] at hlo
      simpa only [mul_comm] using hlo
    have hdhi : D/M ≤ deltaM 1 (sc M S) := by
      apply (div_le_iff₀ hM).mpr
      change D ≤ deltaM M S at hhi
      rw [hr.2.1] at hhi
      simpa only [mul_comm] using hhi
    obtain ⟨ν,hm,hmean,hscale,hdev,_,hp⟩:=ht.2.1 (D/M) ⟨hdlo,hdhi⟩
    apply lift_normalized_attainer μ c S D _ hc hμ
    refine ⟨ν,hm,hmean,hscale,hdev,?_⟩
    have he : medBound M S D=Real.log (sc M S)/(D/M) := by
      unfold medBound
      field_simp
    rw [he,div_mul_eq_mul_div]
    apply (eq_div_iff hDN.ne').mpr
    rw [hdev] at hp
    nlinarith
  · intro hlo hhi
    have hdlo : deltaM 1 (sc M S) ≤ D/M := by
      apply (le_div_iff₀ hM).mpr
      change deltaM M S ≤ D at hlo
      rw [hr.2.1] at hlo
      simpa only [mul_comm] using hlo
    have hdhi : D/M ≤ deltaH 1 (sc M S) := by
      apply (div_le_iff₀ hM).mpr
      change D ≤ deltaH M S at hhi
      rw [hr.2.2] at hhi
      simpa only [mul_comm] using hhi
    obtain ⟨ν,hm,hmean,hscale,hdev,_,hp⟩:=ht.2.2 (D/M) ⟨hdlo,hdhi⟩
    exact lift_normalized_attainer μ c S D _ hc hμ ⟨ν,hm,hmean,hscale,hdev,hp⟩
end Queelius.PersonalizedPricing

end

section
open MeasureTheory Set Filter Topology
namespace ValuePersPricing.Deviation

/-- Theorem 2 (Elmachtoub–Gupta–Hamilton, p. 13): the three-regime upper bound on `R_PP / R_SP` in
terms of scale `S`, margin `M` and coefficient of deviation `D`, stated multiplicatively, with the
unbounded-support case (`S = ∞`, pp. 8 and 13), and tightness of each regime's bound on its closed
interval for every `D > 0` (corrected: at `D = 0` no law has scale `S > 1`). -/
theorem theorem_2 :
    (∀ (ν : Measure ℝ) (c : ℝ), Market ν c → c < mean ν →
      (∀ S : ℝ, 1 < S → IsScale ν S →
        (coefDev ν ≤ deltaL (margin ν c) S →
          ppProfit ν c ≤ lowBound (margin ν c) (coefDev ν) * spProfit ν c) ∧
        (deltaL (margin ν c) S ≤ coefDev ν → coefDev ν ≤ deltaM (margin ν c) S →
          ppProfit ν c ≤ medBound (margin ν c) S (coefDev ν) * spProfit ν c) ∧
        (deltaM (margin ν c) S ≤ coefDev ν → coefDev ν ≤ deltaH (margin ν c) S →
          ppProfit ν c ≤ highBound (margin ν c) S (coefDev ν) * spProfit ν c)) ∧
      (Unbounded ν →
        ppProfit ν c ≤ lowBound (margin ν c) (coefDev ν) * spProfit ν c)) ∧
    (∀ μ c S D : ℝ, 0 ≤ c → c < μ → 1 < S → 0 < D →
      (D ≤ deltaL (1 - c / μ) S →
        ∃ ν : Measure ℝ, Market ν c ∧ mean ν = μ ∧ IsScale ν S ∧ coefDev ν = D ∧
          ppProfit ν c = lowBound (1 - c / μ) D * spProfit ν c) ∧
      (deltaL (1 - c / μ) S ≤ D → D ≤ deltaM (1 - c / μ) S →
        ∃ ν : Measure ℝ, Market ν c ∧ mean ν = μ ∧ IsScale ν S ∧ coefDev ν = D ∧
          ppProfit ν c = medBound (1 - c / μ) S D * spProfit ν c) ∧
      (deltaM (1 - c / μ) S ≤ D → D ≤ deltaH (1 - c / μ) S →
        ∃ ν : Measure ℝ, Market ν c ∧ mean ν = μ ∧ IsScale ν S ∧ coefDev ν = D ∧
          ppProfit ν c = highBound (1 - c / μ) S D * spProfit ν c)) := by
  exact ⟨fun ν c hm hc=>Queelius.PersonalizedPricing.all_regime_upper_bounds ν c hm hc,
    Queelius.PersonalizedPricing.general_tightness⟩

end ValuePersPricing.Deviation

end

section
theorem solution : (
  And
    (∀ (ν : @MeasureTheory.Measure Real Real.measurableSpace) (c : Real),
      ValuePersPricing.Deviation.Market ν c →
        @LT.lt Real Real.instLT c (ValuePersPricing.Deviation.mean ν) →
          And
            (∀ (S : Real),
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S →
                ValuePersPricing.Deviation.IsScale ν S →
                  And
                    (@LE.le Real Real.instLE (ValuePersPricing.Deviation.coefDev ν)
                        (ValuePersPricing.Deviation.deltaL (ValuePersPricing.Deviation.margin ν c) S) →
                      @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                          (ValuePersPricing.Deviation.lowBound (ValuePersPricing.Deviation.margin ν c)
                            (ValuePersPricing.Deviation.coefDev ν))
                          (ValuePersPricing.Deviation.spProfit ν c)))
                    (And
                      (@LE.le Real Real.instLE
                          (ValuePersPricing.Deviation.deltaL (ValuePersPricing.Deviation.margin ν c) S)
                          (ValuePersPricing.Deviation.coefDev ν) →
                        @LE.le Real Real.instLE (ValuePersPricing.Deviation.coefDev ν)
                            (ValuePersPricing.Deviation.deltaM (ValuePersPricing.Deviation.margin ν c) S) →
                          @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                              (ValuePersPricing.Deviation.medBound (ValuePersPricing.Deviation.margin ν c) S
                                (ValuePersPricing.Deviation.coefDev ν))
                              (ValuePersPricing.Deviation.spProfit ν c)))
                      (@LE.le Real Real.instLE
                          (ValuePersPricing.Deviation.deltaM (ValuePersPricing.Deviation.margin ν c) S)
                          (ValuePersPricing.Deviation.coefDev ν) →
                        @LE.le Real Real.instLE (ValuePersPricing.Deviation.coefDev ν)
                            (ValuePersPricing.Deviation.deltaH (ValuePersPricing.Deviation.margin ν c) S) →
                          @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                              (ValuePersPricing.Deviation.highBound (ValuePersPricing.Deviation.margin ν c) S
                                (ValuePersPricing.Deviation.coefDev ν))
                              (ValuePersPricing.Deviation.spProfit ν c)))))
            (ValuePersPricing.Deviation.Unbounded ν →
              @LE.le Real Real.instLE (ValuePersPricing.Deviation.ppProfit ν c)
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (ValuePersPricing.Deviation.lowBound (ValuePersPricing.Deviation.margin ν c)
                    (ValuePersPricing.Deviation.coefDev ν))
                  (ValuePersPricing.Deviation.spProfit ν c))))
    (∀ (μ c S D : Real),
      @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) c →
        @LT.lt Real Real.instLT c μ →
          @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) S →
            @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) D →
              And
                (@LE.le Real Real.instLE D
                    (ValuePersPricing.Deviation.deltaL
                      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c μ))
                      S) →
                  @Exists (@MeasureTheory.Measure Real Real.measurableSpace)
                    fun (ν : @MeasureTheory.Measure Real Real.measurableSpace) =>
                    And (ValuePersPricing.Deviation.Market ν c)
                      (And (@Eq Real (ValuePersPricing.Deviation.mean ν) μ)
                        (And (ValuePersPricing.Deviation.IsScale ν S)
                          (And (@Eq Real (ValuePersPricing.Deviation.coefDev ν) D)
                            (@Eq Real (ValuePersPricing.Deviation.ppProfit ν c)
                              (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                (ValuePersPricing.Deviation.lowBound
                                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                                    (@HDiv.hDiv Real Real Real
                                      (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c μ))
                                  D)
                                (ValuePersPricing.Deviation.spProfit ν c)))))))
                (And
                  (@LE.le Real Real.instLE
                      (ValuePersPricing.Deviation.deltaL
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c
                            μ))
                        S)
                      D →
                    @LE.le Real Real.instLE D
                        (ValuePersPricing.Deviation.deltaM
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c
                              μ))
                          S) →
                      @Exists (@MeasureTheory.Measure Real Real.measurableSpace)
                        fun (ν : @MeasureTheory.Measure Real Real.measurableSpace) =>
                        And (ValuePersPricing.Deviation.Market ν c)
                          (And (@Eq Real (ValuePersPricing.Deviation.mean ν) μ)
                            (And (ValuePersPricing.Deviation.IsScale ν S)
                              (And (@Eq Real (ValuePersPricing.Deviation.coefDev ν) D)
                                (@Eq Real (ValuePersPricing.Deviation.ppProfit ν c)
                                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                    (ValuePersPricing.Deviation.medBound
                                      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                                        (@HDiv.hDiv Real Real Real
                                          (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c μ))
                                      S D)
                                    (ValuePersPricing.Deviation.spProfit ν c)))))))
                  (@LE.le Real Real.instLE
                      (ValuePersPricing.Deviation.deltaM
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c
                            μ))
                        S)
                      D →
                    @LE.le Real Real.instLE D
                        (ValuePersPricing.Deviation.deltaH
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c
                              μ))
                          S) →
                      @Exists (@MeasureTheory.Measure Real Real.measurableSpace)
                        fun (ν : @MeasureTheory.Measure Real Real.measurableSpace) =>
                        And (ValuePersPricing.Deviation.Market ν c)
                          (And (@Eq Real (ValuePersPricing.Deviation.mean ν) μ)
                            (And (ValuePersPricing.Deviation.IsScale ν S)
                              (And (@Eq Real (ValuePersPricing.Deviation.coefDev ν) D)
                                (@Eq Real (ValuePersPricing.Deviation.ppProfit ν c)
                                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                    (ValuePersPricing.Deviation.highBound
                                      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                                        (@HDiv.hDiv Real Real Real
                                          (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) c μ))
                                      S D)
                                    (ValuePersPricing.Deviation.spProfit ν c)))))))))
) := @ValuePersPricing.Deviation.theorem_2

end
