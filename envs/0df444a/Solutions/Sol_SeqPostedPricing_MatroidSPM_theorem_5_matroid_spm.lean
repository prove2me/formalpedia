-- Prove2me | solution 1 for SeqPostedPricing.MatroidSPM.theorem_5_matroid_spm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T00:12:38.86659+00:00
-- url     : https://prove2.me/submissions/d49e81f6-51cf-4283-abf8-123df168c5ee

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsRegular
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsOptimal
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsQuantilePrice
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmActive
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmRevenue
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsDecreasingOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.all false


open MeasureTheory Set

namespace B170C

lemma setLIntegral_eq_of' {s : Set ℝ} {μ : Measure ℝ} (hs : MeasurableSet s) {f g : ℝ → ENNReal}
    (h : ∀ x ∈ s, f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
  le_antisymm (setLIntegral_mono' hs fun x hx => (h x hx).le)
    (setLIntegral_mono' hs fun x hx => (h x hx).ge)

/-- Layer identity: `∫_{(x,y]} ν(t,∞) dt = ∫_{(x,y]} (s-x) dν + (y-x) ν(y,∞)`. -/
lemma layerJ (ν : Measure ℝ) [IsFiniteMeasure ν] (x y : ℝ) (hxy : x ≤ y) :
    ∫⁻ t in Ioc x y, ν (Ioi t) =
      ∫⁻ s in Ioc x y, ENNReal.ofReal (s - x) ∂ν + ENNReal.ofReal (y - x) * ν (Ioi y) := by
  have h1 : ∀ t, ν (Ioi t) = ∫⁻ s, (Ioi t).indicator 1 s ∂ν := by
    intro t; rw [lintegral_indicator measurableSet_Ioi]; simp
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun (t s : ℝ) => (Ioi t).indicator (1 : ℝ → ENNReal) s) := by
    have : (Function.uncurry fun (t s : ℝ) => (Ioi t).indicator (1 : ℝ → ENNReal) s)
        = {z : ℝ × ℝ | z.1 < z.2}.indicator 1 := by
      funext z; obtain ⟨t, s⟩ := z; simp [Set.indicator_apply]
    rw [this]; exact measurable_one.indicator (measurableSet_lt measurable_fst measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ s, ∫⁻ t in Ioc x y, (Ioi t).indicator (1 : ℝ → ENNReal) s
      = (Ioc x y).indicator (fun s => ENNReal.ofReal (s - x)) s
        + (Ioi y).indicator (fun _ => ENNReal.ofReal (y - x)) s := by
    intro s
    have : (fun t => (Ioi t).indicator (1 : ℝ → ENNReal) s) = (Iio s).indicator 1 := by
      funext t; simp [Set.indicator_apply]
    rw [this, lintegral_indicator measurableSet_Iio]
    simp only [Pi.one_apply]
    rw [setLIntegral_one, Measure.restrict_apply measurableSet_Iio]
    rcases le_or_gt s x with hsx | hsx
    · have he : Iio s ∩ Ioc x y = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun u hu => ?_
        simp only [mem_inter_iff, mem_Iio, mem_Ioc] at hu
        linarith [hu.1, hu.2.1]
      have hn1 : s ∉ Ioc x y := fun h => by simp only [mem_Ioc] at h; linarith [h.1]
      have hn2 : s ∉ Ioi y := fun h => by simp only [mem_Ioi] at h; linarith
      rw [he, measure_empty, indicator_of_notMem hn1, indicator_of_notMem hn2, add_zero]
    rcases le_or_gt s y with hsy | hsy
    · have he : Iio s ∩ Ioc x y = Ioo x s := by
        ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, by linarith [h.2]⟩⟩
      have hm1 : s ∈ Ioc x y := ⟨hsx, hsy⟩
      have hn2 : s ∉ Ioi y := fun h => by simp only [mem_Ioi] at h; linarith
      rw [he, Real.volume_Ioo, indicator_of_mem hm1, indicator_of_notMem hn2, add_zero]
    · have he : Iio s ∩ Ioc x y = Ioc x y := by
        ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioc]
        exact ⟨fun h => h.2, fun h => ⟨by linarith [h.2], h⟩⟩
      have hn1 : s ∉ Ioc x y := fun h => by simp only [mem_Ioc] at h; linarith [h.2]
      have hm2 : s ∈ Ioi y := hsy
      rw [he, Real.volume_Ioc, indicator_of_notMem hn1, indicator_of_mem hm2, zero_add]
  rw [lintegral_congr h2]
  have hm1 : Measurable ((Ioc x y).indicator (fun s => ENNReal.ofReal (s - x))) :=
    (show Measurable fun s : ℝ => ENNReal.ofReal (s - x) from
      ENNReal.measurable_ofReal.comp (measurable_id.sub_const x)).indicator measurableSet_Ioc
  rw [lintegral_add_left hm1, lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioi,
    setLIntegral_const, ← h1 y]

lemma setLIntegral_ofReal_sub_ne_top (ν : Measure ℝ) [IsFiniteMeasure ν] (x y : ℝ) :
    ∫⁻ s in Ioc x y, ENNReal.ofReal (s - x) ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioc x y, ENNReal.ofReal (y - x) ∂ν) ?_ ?_
  · rw [setLIntegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · exact setLIntegral_mono' measurableSet_Ioc fun s hs => ENNReal.ofReal_le_ofReal (by linarith [hs.2])

/-- Key single-agent inequality: for a regular law and an interior price `p` there is `c < p`
with `(θ - c) ν[θ,∞) ≤ (p - c) ν(p,∞)` for every `θ`. -/
lemma keyK (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hreg : SeqPostedPricing.MatroidSPM.IsRegular ν) (p : ℝ)
    (hq0 : 0 < (ν (Ioi p)).toReal) (hq1 : (ν (Ioi p)).toReal < 1) :
    ∃ c, c < p ∧ ∀ θ, (θ - c) * (ν (Ici θ)).toReal ≤ (p - c) * (ν (Ioi p)).toReal := by
  obtain ⟨f, hfm, hf0, hν, hpos, hmono⟩ := hreg
  have hFG : ∀ t, (ν (Iic t)).toReal + (ν (Ioi t)).toReal = 1 := by
    intro t
    have := prob_add_prob_compl (μ := ν) (measurableSet_Iic (a := t))
    rw [compl_Iic] at this
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), this, ENNReal.toReal_one]
  have hFmono : Monotone fun t => (ν (Iic t)).toReal := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hab))
  have hFm : Measurable fun t => (ν (Iic t)).toReal := hFmono.measurable
  have hfm' : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hfm
  have : NullSingletonClass ν := ⟨fun t => by
    rw [hν]; exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)⟩
  have hIci : ∀ θ, ν (Ici θ) = ν (Ioi θ) := fun θ => (measure_congr Ioi_ae_eq_Ici).symm
  have hIp : 0 < (ν (Iic p)).toReal ∧ (ν (Iic p)).toReal < 1 := by
    constructor <;> linarith [hFG p]
  have hfp : 0 < f p := hpos p hIp.1 hIp.2
  have hφ_eq : ∀ t, 0 < f t →
      1 - (ν (Iic t)).toReal = (t - (t - (1 - (ν (Iic t)).toReal) / f t)) * f t := by
    intro t ht; rw [sub_sub_cancel, div_mul_cancel₀ _ ht.ne']
  obtain ⟨c, hc⟩ : ∃ c, c = p - (1 - (ν (Iic p)).toReal) / f p := ⟨_, rfl⟩
  have hcp : c < p := by
    have : 0 < (1 - (ν (Iic p)).toReal) / f p := div_pos (by linarith [hIp.2]) hfp
    linarith
  -- pointwise bound above p
  have P1 : ∀ t, p ≤ t → (ν (Ioi t)).toReal ≤ (t - c) * f t := by
    intro t hpt
    by_cases hFt : (ν (Iic t)).toReal < 1
    · have hFt0 : 0 < (ν (Iic t)).toReal := lt_of_lt_of_le hIp.1 (hFmono hpt)
      have hft := hpos t hFt0 hFt
      have hm := hmono hIp ⟨hFt0, hFt⟩ hpt
      simp only at hm
      rw [show (ν (Ioi t)).toReal = 1 - (ν (Iic t)).toReal by linarith [hFG t], hφ_eq t hft]
      exact mul_le_mul_of_nonneg_right (by linarith) hft.le
    · have : (ν (Ioi t)).toReal ≤ 0 := by linarith [hFG t]
      exact this.trans (mul_nonneg (by linarith) (hf0 t))
  -- the null bottom region
  have hZ : ν {t | t ≤ p ∧ (ν (Iic t)).toReal ≤ 0} = 0 := by
    set Z := {t | t ≤ p ∧ (ν (Iic t)).toReal ≤ 0} with hZdef
    rcases Z.eq_empty_or_nonempty with h | hne
    · rw [h, measure_empty]
    have hbdd : BddAbove Z := ⟨p, fun t ht => ht.1⟩
    have hz : ∀ z ∈ Z, ν (Iic z) = 0 := fun z hz => by
      rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hz.2 ENNReal.toReal_nonneg) with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    have h1 : Z ⊆ (⋃ n : ℕ, Iic (sSup Z - 1 / ((n : ℝ) + 1))) ∪ {sSup Z} := by
      intro t ht
      have hts : t ≤ sSup Z := le_csSup hbdd ht
      rcases hts.lt_or_eq with h | h
      · left
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact mem_iUnion.2 ⟨n, by simp only [mem_Iic]; linarith⟩
      · right; exact h
    refine measure_mono_null h1 (measure_union_null (measure_iUnion_null fun n => ?_)
      (measure_singleton _))
    have hpos' : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨z, hzZ, hz'⟩ := exists_lt_of_lt_csSup hne (show sSup Z - 1 / ((n : ℝ) + 1) < sSup Z by
      linarith)
    exact measure_mono_null (Iic_subset_Iic.2 hz'.le) (hz z hzZ)
  have hZm : MeasurableSet {t : ℝ | t ≤ p ∧ (ν (Iic t)).toReal ≤ 0} :=
    (measurableSet_le measurable_id measurable_const).inter (measurableSet_le hFm measurable_const)
  have hZf : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ {t : ℝ | t ≤ p ∧ (ν (Iic t)).toReal ≤ 0} → f t = 0 := by
    have h0 : ∫⁻ t in {t : ℝ | t ≤ p ∧ (ν (Iic t)).toReal ≤ 0}, ENNReal.ofReal (f t) = 0 := by
      rw [← withDensity_apply _ hZm, ← hν]; exact hZ
    have := (lintegral_eq_zero_iff hfm').1 h0
    rw [Filter.EventuallyEq, ae_restrict_iff' hZm] at this
    filter_upwards [this] with t ht htZ
    have h' := ht htZ
    simp only [Function.comp_apply, Pi.zero_apply, ENNReal.ofReal_eq_zero] at h'
    exact le_antisymm h' (hf0 t)
  -- density rewriting
  have hwd : ∀ (g : ℝ → ENNReal), Measurable g → ∀ s : Set ℝ, MeasurableSet s →
      ∫⁻ t in s, g t ∂ν = ∫⁻ t in s, ENNReal.ofReal (f t) * g t := by
    intro g hg s hs
    rw [hν, setLIntegral_withDensity_eq_setLIntegral_mul _ hfm' hg hs]
    rfl
  have hsplit : ∀ a b : ℝ, c ≤ a →
      ∫⁻ t in Ioc a b, ENNReal.ofReal ((t - c) * f t)
        = ENNReal.ofReal (a - c) * ν (Ioc a b) + ∫⁻ t in Ioc a b, ENNReal.ofReal (t - a) ∂ν := by
    intro a b hca
    have e1 : ∫⁻ t in Ioc a b, ENNReal.ofReal ((t - c) * f t)
        = ∫⁻ t in Ioc a b, ENNReal.ofReal (t - c) ∂ν := by
      have hgc : Measurable fun t : ℝ => ENNReal.ofReal (t - c) :=
        ENNReal.measurable_ofReal.comp (measurable_id.sub_const c)
      have hw := hwd (fun t => ENNReal.ofReal (t - c)) hgc (Ioc a b) measurableSet_Ioc
      rw [hw]
      refine setLIntegral_eq_of' measurableSet_Ioc fun t ht => ?_
      rw [ENNReal.ofReal_mul (by linarith [ht.1]), mul_comm]
    rw [e1]
    have e2 : ∫⁻ t in Ioc a b, ENNReal.ofReal (t - c) ∂ν
        = ∫⁻ t in Ioc a b, (ENNReal.ofReal (a - c) + ENNReal.ofReal (t - a)) ∂ν := by
      refine setLIntegral_eq_of' measurableSet_Ioc fun t ht => ?_
      rw [← ENNReal.ofReal_add (by linarith) (by linarith [ht.1])]; congr 1; ring
    rw [e2, lintegral_add_left measurable_const, setLIntegral_const]
  refine ⟨c, hcp, fun θ => ?_⟩
  rw [hIci θ]
  have hG0 : ∀ t, 0 ≤ (ν (Ioi t)).toReal := fun t => ENNReal.toReal_nonneg
  have hRHS : 0 < (p - c) * (ν (Ioi p)).toReal := mul_pos (by linarith) hq0
  rcases le_or_gt θ c with hθc | hθc
  · have : (θ - c) * (ν (Ioi θ)).toReal ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (hG0 θ)
    linarith
  rcases le_or_gt p θ with hpθ | hθp
  · -- θ ≥ p
    have hJ := layerJ ν p θ hpθ
    have hcmp : ∫⁻ t in Ioc p θ, ν (Ioi t) ≤ ∫⁻ t in Ioc p θ, ENNReal.ofReal ((t - c) * f t) :=
      setLIntegral_mono' measurableSet_Ioc fun t ht => by
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν (Ioi t))]
        exact ENNReal.ofReal_le_ofReal (P1 t ht.1.le)
    rw [hJ, hsplit p θ hcp.le, add_comm (ENNReal.ofReal (p - c) * ν (Ioc p θ))] at hcmp
    have hA := (ENNReal.add_le_add_iff_left (setLIntegral_ofReal_sub_ne_top ν p θ)).1 hcmp
    have hdec : ν (Ioi p) = ν (Ioc p θ) + ν (Ioi θ) := by
      rw [← Ioc_union_Ioi_eq_Ioi hpθ, measure_union _ measurableSet_Ioi]
      exact Set.disjoint_left.2 fun u hu hu' => by
        simp only [mem_Ioc, mem_Ioi] at hu hu'; linarith [hu.2]
    have hAr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hA
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)] at hAr
    have hdr : (ν (Ioi p)).toReal = (ν (Ioc p θ)).toReal + (ν (Ioi θ)).toReal := by
      rw [hdec, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [hdr]; nlinarith
  · -- c < θ < p
    have hJ := layerJ ν θ p hθp.le
    have hcmp : ∫⁻ t in Ioc θ p, ENNReal.ofReal ((t - c) * f t) ≤ ∫⁻ t in Ioc θ p, ν (Ioi t) := by
      refine setLIntegral_mono_ae' measurableSet_Ioc ?_
      filter_upwards [hZf] with t htZ ht
      rw [← ENNReal.ofReal_toReal (measure_ne_top ν (Ioi t))]
      apply ENNReal.ofReal_le_ofReal
      by_cases hFt0 : 0 < (ν (Iic t)).toReal
      · have hFt1 : (ν (Iic t)).toReal < 1 := lt_of_le_of_lt (hFmono ht.2) hIp.2
        have hft := hpos t hFt0 hFt1
        have hm := hmono ⟨hFt0, hFt1⟩ hIp ht.2
        simp only at hm
        rw [show (ν (Ioi t)).toReal = 1 - (ν (Iic t)).toReal by linarith [hFG t], hφ_eq t hft]
        exact mul_le_mul_of_nonneg_right (by linarith) hft.le
      · have : f t = 0 := htZ ⟨ht.2, not_lt.1 hFt0⟩
        rw [this, mul_zero]; exact hG0 t
    rw [hJ, hsplit θ p hθc.le, add_comm (ENNReal.ofReal (θ - c) * ν (Ioc θ p))] at hcmp
    have hA := (ENNReal.add_le_add_iff_left (setLIntegral_ofReal_sub_ne_top ν θ p)).1 hcmp
    have hdec : ν (Ioi θ) = ν (Ioc θ p) + ν (Ioi p) := by
      rw [← Ioc_union_Ioi_eq_Ioi hθp.le, measure_union _ measurableSet_Ioi]
      exact Set.disjoint_left.2 fun u hu hu' => by
        simp only [mem_Ioc, mem_Ioi] at hu hu'; linarith [hu.2]
    have hAr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hA
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)] at hAr
    have hdr : (ν (Ioi θ)).toReal = (ν (Ioc θ p)).toReal + (ν (Ioi p)).toReal := by
      rw [hdec, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [hdr]; nlinarith

end B170C

open MeasureTheory Set SeqPostedPricing.MatroidSPM

namespace B170C

lemma update_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Function.update_self]; exact measurable_snd
  · simp only [Function.update_of_ne h]; exact (measurable_pi_apply j).comp measurable_fst

lemma update_mp {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨update_measurable i, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (update_measurable i) (MeasurableSet.univ_pi hs)]
  have hpre : (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2) ⁻¹' (univ.pi s)
      = (univ.pi (Function.update s i univ)) ×ˢ (s i) := by
    ext ⟨v, w⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp
        · rw [Function.update_of_ne hj]; have := h j; rwa [Function.update_of_ne hj] at this
      · have := h i; rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; rwa [Function.update_self]
      · rw [Function.update_of_ne hj]; have := h1 j; rwa [Function.update_of_ne hj] at this
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i), Function.update_self, measure_univ,
    one_mul, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => μ j (s j)), mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have : j ≠ i := by simpa using hj
  rw [Function.update_of_ne this]

lemma integral_update {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n)
    {g : (Fin n → ℝ) → ℝ} (hg : Integrable g (Measure.pi μ)) :
    ∫ v, g v ∂(Measure.pi μ) = ∫ v, (∫ w, g (Function.update v i w) ∂(μ i)) ∂(Measure.pi μ)
    ∧ Integrable (fun v => ∫ w, g (Function.update v i w) ∂(μ i)) (Measure.pi μ)
    ∧ ∀ᵐ v ∂(Measure.pi μ), Integrable (fun w => g (Function.update v i w)) (μ i) := by
  have hmp := update_mp μ i
  have hgc : Integrable (fun z : (Fin n → ℝ) × ℝ => g (Function.update z.1 i z.2))
      ((Measure.pi μ).prod (μ i)) :=
    (hmp.integrable_comp hg.aestronglyMeasurable).2 hg
  refine ⟨?_, hgc.integral_prod_left, hgc.prod_right_ae⟩
  have e : ∫ v, g v ∂(Measure.pi μ)
      = ∫ z, g (Function.update z.1 i z.2) ∂((Measure.pi μ).prod (μ i)) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [e, integral_prod _ hgc]

lemma ae_update {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n)
    {P : (Fin n → ℝ) → Prop} (h : ∀ᵐ v ∂(Measure.pi μ), P v) :
    ∀ᵐ v ∂(Measure.pi μ), ∀ᵐ w ∂(μ i), P (Function.update v i w) :=
  Measure.ae_ae_of_ae_prod ((update_mp μ i).quasiMeasurePreserving.ae h)

lemma section_bound (ν : Measure ℝ) [IsProbabilityMeasure ν] (pay : ℝ → ℝ) (S W : Set ℝ)
    (hS : MeasurableSet S) (hW : ∀ᵐ w ∂ν, w ∈ W)
    (h1 : ∀ w ∈ W, w ∈ S → ∀ w' ∈ W, w' ∈ S → pay w ≤ w')
    (h2 : ∀ w ∈ W, w ∉ S → pay w ≤ 0)
    (c K : ℝ) (hK : ∀ θ, c < θ → (θ - c) * (ν (Ici θ)).toReal ≤ K) (hK0 : 0 ≤ K)
    (hint : Integrable (fun w => pay w - c * S.indicator 1 w) ν) :
    ∫ w, (pay w - c * S.indicator 1 w) ∂ν ≤ K := by
  have hcov : S ⊆ (S ∩ W) ∪ {w | w ∉ W} := fun w hw => by
    by_cases h : w ∈ W
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr h
  by_cases hS0 : ν S = 0
  · have : ∀ᵐ w ∂ν, pay w - c * S.indicator 1 w ≤ 0 := by
      have hnS : ∀ᵐ w ∂ν, w ∉ S := measure_eq_zero_iff_ae_notMem.1 hS0
      filter_upwards [hW, hnS] with w hw hns
      rw [indicator_of_notMem hns, mul_zero, sub_zero]; exact h2 w hw hns
    exact (integral_nonpos_of_ae this).trans hK0
  · have hne : (S ∩ W).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      apply hS0
      exact measure_mono_null hcov (by rw [hcon, empty_union]; exact ae_iff.1 hW)
    obtain ⟨w0, hw0S, hw0W⟩ := hne
    have hbdd : BddBelow (S ∩ W) := ⟨pay w0, fun w' hw' => h1 w0 hw0W hw0S w' hw'.2 hw'.1⟩
    have hpayθ : ∀ w ∈ W, w ∈ S → pay w ≤ sInf (S ∩ W) := fun w hw hs =>
      le_csInf ⟨w0, hw0S, hw0W⟩ fun w' hw' => h1 w hw hs w' hw'.2 hw'.1
    have hle : ∀ᵐ w ∂ν, pay w - c * S.indicator 1 w ≤ (sInf (S ∩ W) - c) * S.indicator 1 w := by
      filter_upwards [hW] with w hw
      by_cases hs : w ∈ S
      · rw [indicator_of_mem hs]; simp only [Pi.one_apply, mul_one]; linarith [hpayθ w hw hs]
      · rw [indicator_of_notMem hs, mul_zero, mul_zero, sub_zero]; exact h2 w hw hs
    have hint2 : Integrable (fun w => (sInf (S ∩ W) - c) * S.indicator 1 w) ν :=
      ((integrable_const (1 : ℝ)).indicator hS).const_mul _
    have h3 := integral_mono_ae hint hint2 hle
    rw [integral_const_mul, integral_indicator_one hS] at h3
    refine h3.trans ?_
    rw [measureReal_def]
    rcases le_or_gt (sInf (S ∩ W)) c with hθ | hθ
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg).trans hK0
    · refine le_trans ?_ (hK _ hθ)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      calc ν S ≤ ν ((S ∩ W) ∪ {w | w ∉ W}) := measure_mono hcov
        _ ≤ ν (S ∩ W) + ν {w | w ∉ W} := measure_union_le _ _
        _ = ν (S ∩ W) := by rw [ae_iff.1 hW, add_zero]
        _ ≤ ν (Ici (sInf (S ∩ W))) := measure_mono fun w hw => csInf_le hbdd hw

lemma section_full (ν : Measure ℝ) [IsProbabilityMeasure ν] (pay : ℝ → ℝ) (S W : Set ℝ)
    (hfull : ∀ᵐ w ∂ν, w ∈ S ∧ w ∈ W)
    (h1 : ∀ w ∈ W, w ∈ S → ∀ w' ∈ W, w' ∈ S → pay w ≤ w')
    (p : ℝ) (hp : ∀ p', p < p' → (ν (Ioi p')).toReal < 1) (hint : Integrable pay ν) :
    ∫ w, pay w ∂ν ≤ p := by
  have h0 := ae_iff.1 hfull
  have hne : (S ∩ W).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hu : {a | ¬(a ∈ S ∧ a ∈ W)} = univ := by
      ext a
      simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h
      have : a ∈ S ∩ W := ⟨h.1, h.2⟩
      rw [hcon] at this; exact this
    rw [hu, measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨w0, hw0S, hw0W⟩ := hne
  have hbdd : BddBelow (S ∩ W) := ⟨pay w0, fun w' hw' => h1 w0 hw0W hw0S w' hw'.2 hw'.1⟩
  have hpayθ : ∀ w ∈ W, w ∈ S → pay w ≤ sInf (S ∩ W) := fun w hw hs =>
    le_csInf ⟨w0, hw0S, hw0W⟩ fun w' hw' => h1 w hw hs w' hw'.2 hw'.1
  have hle : ∀ᵐ w ∂ν, pay w ≤ sInf (S ∩ W) := by
    filter_upwards [hfull] with w hw; exact hpayθ w hw.2 hw.1
  have h3 : ∫ w, pay w ∂ν ≤ sInf (S ∩ W) := by
    simpa using integral_mono_ae hint (integrable_const (sInf (S ∩ W))) hle
  refine h3.trans ?_
  by_contra hθp
  rw [not_le] at hθp
  have hsub : univ ⊆ Ioi ((p + sInf (S ∩ W)) / 2) ∪ {a | ¬(a ∈ S ∧ a ∈ W)} := fun a _ => by
    by_cases h : a ∈ S ∧ a ∈ W
    · left
      have := csInf_le hbdd ⟨h.1, h.2⟩
      simp only [mem_Ioi]; linarith
    · right; exact h
  have h1' : (1 : ENNReal) ≤ ν (Ioi ((p + sInf (S ∩ W)) / 2)) := by
    calc (1 : ENNReal) = ν univ := measure_univ.symm
      _ ≤ ν (Ioi ((p + sInf (S ∩ W)) / 2) ∪ {a | ¬(a ∈ S ∧ a ∈ W)}) := measure_mono hsub
      _ ≤ ν (Ioi ((p + sInf (S ∩ W)) / 2)) + ν {a | ¬(a ∈ S ∧ a ∈ W)} := measure_union_le _ _
      _ = ν (Ioi ((p + sInf (S ∩ W)) / 2)) := by rw [h0, add_zero]
  have h2' : 1 ≤ (ν (Ioi ((p + sInf (S ∩ W)) / 2))).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) h1'
    simpa using this
  linarith [hp ((p + sInf (S ∩ W)) / 2) (by linarith)]

/-- Profiles where truthfulness and individual rationality hold. -/
def GoodSet {n : ℕ} (M : Mechanism n) : Set (Fin n → ℝ) :=
  {v | (∀ i w, utility M i (v i) (Function.update v i w) ≤ utility M i (v i) v) ∧
    ∀ i, 0 ≤ utility M i (v i) v}

lemma good_h1 {n : ℕ} (M : Mechanism n) (i : Fin n) (v : Fin n → ℝ) (w w' : ℝ)
    (hw : Function.update v i w ∈ GoodSet M) (hs : i ∈ M.alloc (Function.update v i w))
    (hw' : Function.update v i w' ∈ GoodSet M) (hs' : i ∈ M.alloc (Function.update v i w')) :
    M.pay (Function.update v i w) i ≤ w' := by
  have t := hw.1 i w'
  rw [Function.update_idem, Function.update_self] at t
  have ir := hw'.2 i
  rw [Function.update_self] at ir
  simp only [utility, if_pos hs, if_pos hs'] at t ir
  linarith

lemma good_h2 {n : ℕ} (M : Mechanism n) (i : Fin n) (v : Fin n → ℝ) (w : ℝ)
    (hw : Function.update v i w ∈ GoodSet M) (hs : i ∉ M.alloc (Function.update v i w)) :
    M.pay (Function.update v i w) i ≤ 0 := by
  have ir := hw.2 i
  rw [Function.update_self] at ir
  simp only [utility, if_neg hs] at ir
  linarith

section Agent
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (M : Mechanism n)

lemma good_ae (hT : IsTruthful M) (hIR : IsIndividuallyRational M) :
    ∀ᵐ v ∂(Measure.pi μ), v ∈ GoodSet M := by
  exact Filter.Eventually.of_forall fun v => ⟨fun i w => hT v i w, fun i => hIR v i⟩

lemma pay_bound_interior (hT : IsTruthful M) (hIR : IsIndividuallyRational M)
    (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v})
    (hint : ∀ i, Integrable (fun v => M.pay v i) (Measure.pi μ)) (i : Fin n) (c K : ℝ)
    (hK : ∀ θ, c < θ → (θ - c) * ((μ i) (Ici θ)).toReal ≤ K) (hK0 : 0 ≤ K) :
    ∫ v, M.pay v i ∂(Measure.pi μ) ≤ c * allocProb μ M i + K := by
  have hA : MeasurableSet {v | i ∈ M.alloc v} := hmeas i
  have hI1 : Integrable ({v | i ∈ M.alloc v}.indicator (1 : (Fin n → ℝ) → ℝ)) (Measure.pi μ) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hI2 : Integrable (fun v => c * {v | i ∈ M.alloc v}.indicator (1 : (Fin n → ℝ) → ℝ) v)
      (Measure.pi μ) := hI1.const_mul c
  have hΦ : Integrable (fun v => M.pay v i - c * {v | i ∈ M.alloc v}.indicator 1 v) (Measure.pi μ) :=
    (hint i).sub hI2
  obtain ⟨e, hInt, hsec⟩ := integral_update μ i hΦ
  have hgood := ae_update μ i (good_ae μ M hT hIR)
  have hbound : ∀ᵐ v ∂(Measure.pi μ),
      ∫ w, (M.pay (Function.update v i w) i
        - c * {v | i ∈ M.alloc v}.indicator 1 (Function.update v i w)) ∂(μ i) ≤ K := by
    filter_upwards [hgood, hsec] with v hv hvi
    exact section_bound (μ i) (fun w => M.pay (Function.update v i w) i)
      ((fun w => Function.update v i w) ⁻¹' {v | i ∈ M.alloc v})
      {w | Function.update v i w ∈ GoodSet M} (hA.preimage (measurable_update v)) hv
      (fun w hw hs w' hw' hs' => good_h1 M i v w w' hw hs hw' hs')
      (fun w hw hs => good_h2 M i v w hw hs) c K hK hK0 hvi
  have h4 := integral_mono_ae hInt (integrable_const K) hbound
  rw [← e] at h4
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h4
  rw [integral_sub (hint i) hI2,
    integral_const_mul, integral_indicator_one hA, measureReal_def] at h4
  unfold allocProb
  linarith

lemma pay_bound_full (hT : IsTruthful M) (hIR : IsIndividuallyRational M)
    (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v})
    (hint : ∀ i, Integrable (fun v => M.pay v i) (Measure.pi μ)) (i : Fin n)
    (hq : allocProb μ M i = 1) (p : ℝ) (hp : ∀ p', p < p' → ((μ i) (Ioi p')).toReal < 1) :
    ∫ v, M.pay v i ∂(Measure.pi μ) ≤ p := by
  have hA : MeasurableSet {v | i ∈ M.alloc v} := hmeas i
  have hP1 : Measure.pi μ {v | i ∈ M.alloc v} = 1 := by
    unfold allocProb at hq
    exact (ENNReal.toReal_eq_one_iff _).1 hq
  have hfullA : ∀ᵐ v ∂(Measure.pi μ), v ∈ {v | i ∈ M.alloc v} := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff hA).2 hP1
    simpa [compl_setOf] using this
  obtain ⟨e, hInt, hsec⟩ := integral_update μ i (hint i)
  have hgood := ae_update μ i ((good_ae μ M hT hIR).and hfullA)
  have hbound : ∀ᵐ v ∂(Measure.pi μ), ∫ w, M.pay (Function.update v i w) i ∂(μ i) ≤ p := by
    filter_upwards [hgood, hsec] with v hv hvi
    exact section_full (μ i) (fun w => M.pay (Function.update v i w) i)
      ((fun w => Function.update v i w) ⁻¹' {v | i ∈ M.alloc v})
      {w | Function.update v i w ∈ GoodSet M}
      (by filter_upwards [hv] with w hw using ⟨hw.2, hw.1⟩)
      (fun w hw hs w' hw' hs' => good_h1 M i v w w' hw hs hw' hs') p hp hvi
  have h4 := integral_mono_ae hInt (integrable_const p) hbound
  rw [← e] at h4
  simpa using h4

lemma pay_bound_zero (hIR : IsIndividuallyRational M)
    (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (i : Fin n) (hq : allocProb μ M i = 0) :
    ∫ v, M.pay v i ∂(Measure.pi μ) ≤ 0 := by
  have hP0 : Measure.pi μ {v | i ∈ M.alloc v} = 0 := by
    unfold allocProb at hq
    rcases (ENNReal.toReal_eq_zero_iff _).1 hq with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hn : ∀ᵐ v ∂(Measure.pi μ), v ∉ {v | i ∈ M.alloc v} := measure_eq_zero_iff_ae_notMem.1 hP0
  refine integral_nonpos_of_ae ?_
  filter_upwards [hn] with v hvn
  have := hIR v i
  simp only [utility, mem_setOf_eq] at this hvn
  rw [if_neg hvn] at this
  simp only [Pi.zero_apply]; linarith

lemma pay_nonneg {Feas : Finset (Fin n) → Prop} (hM : IsOptimal Feas μ M)
    (hdown : ∀ S i, Feas S → Feas (S.erase i)) (i : Fin n) :
    0 ≤ ∫ v, M.pay v i ∂(Measure.pi μ) := by
  obtain ⟨⟨hF, hT, hIR, hmeas, hint⟩, hopt⟩ := hM
  let M' : Mechanism n := ⟨fun v => (M.alloc v).erase i, fun v j => if j = i then 0 else M.pay v j⟩
  have hut : ∀ j x b, utility M' j x b = if j = i then 0 else utility M j x b := by
    intro j x b
    by_cases hj : j = i
    · subst hj; simp [utility, M']
    · simp [utility, M', hj, Finset.mem_erase]
  have hadm : IsAdmissible Feas μ M' := by
    refine ⟨fun v => hdown _ _ (hF v), ?_, ?_, ?_, ?_⟩
    · intro v j w
      rw [hut, hut]
      split_ifs
      · exact le_rfl
      · exact hT v j w
    · intro v j
      rw [hut]
      split_ifs
      · exact le_rfl
      · exact hIR v j
    · intro j
      by_cases hj : j = i
      · subst hj
        have : {v | j ∈ M'.alloc v} = ∅ := by
          ext v; simp [M']
        rw [this]; exact MeasurableSet.empty
      · have : {v | j ∈ M'.alloc v} = {v | j ∈ M.alloc v} := by
          ext v; simp [M', Finset.mem_erase, hj]
        rw [this]; exact hmeas j
    · intro j
      by_cases hj : j = i
      · simp only [M', hj, if_true]; exact integrable_zero _ _ _
      · simp only [M', hj, if_false]; exact hint j
  have h := hopt M' hadm
  unfold revenue at h
  have hsum : ∀ v, ∑ j, M'.pay v j = ∑ j, M.pay v j - M.pay v i := by
    intro v
    have e1 : ∑ j, M.pay v j = ∑ j, ((if j = i then 0 else M.pay v j) + (if j = i then M.pay v j else 0)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [e1, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
    simp [M']
  simp_rw [hsum] at h
  rw [integral_sub (integrable_finset_sum _ fun j _ => hint j) (hint i)] at h
  linarith

end Agent

end B170C

open MeasureTheory Set

namespace B170C
/-- Threshold (Abel) lemma: nonnegative upper-set sums give a nonnegative weighted sum. -/
lemma abel_threshold {ι : Type*} [DecidableEq ι] : ∀ (N : ℕ) (s : Finset ι) (p d : ι → ℝ),
    s.card ≤ N → (∀ i ∈ s, 0 ≤ p i) →
    (∀ t : ℝ, 0 ≤ ∑ i ∈ s.filter (fun i => t < p i), d i) → 0 ≤ ∑ i ∈ s, p i * d i := by
  intro N
  induction N with
  | zero =>
    intro s p d hc _ _
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hc), Finset.sum_empty]
  | succ N ih =>
    intro s p d hc hp h
    rcases s.eq_empty_or_nonempty with hs | hne
    · rw [hs, Finset.sum_empty]
    obtain ⟨i0, hi0, hmin⟩ := s.exists_min_image p hne
    have hm0 : 0 ≤ p i0 := hp i0 hi0
    have hs'card : (s.filter (fun i => p i0 < p i)).card ≤ N := by
      have hss : s.filter (fun i => p i0 < p i) ⊂ s := Finset.filter_ssubset.2 ⟨i0, hi0, lt_irrefl _⟩
      have := Finset.card_lt_card hss
      omega
    have hsplit : ∑ i ∈ s, p i * d i = p i0 * ∑ i ∈ s, d i
        + ∑ i ∈ s.filter (fun i => p i0 < p i), (p i - p i0) * d i := by
      have e1 : ∑ i ∈ s, p i * d i = ∑ i ∈ s, (p i0 * d i + (p i - p i0) * d i) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_filter_add_sum_filter_not s (fun i => p i0 < p i)
        (fun i => (p i - p i0) * d i)]
      have e2 : ∑ i ∈ s.filter (fun i => ¬ p i0 < p i), (p i - p i0) * d i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_filter] at hi
        have : p i = p i0 := le_antisymm (not_lt.1 hi.2) (hmin i hi.1)
        rw [this, sub_self, zero_mul]
      rw [e2, add_zero]
    have h1 : 0 ≤ ∑ i ∈ s, d i := by
      have := h (p i0 - 1)
      rwa [Finset.filter_true_of_mem (fun i hi => by linarith [hmin i hi])] at this
    have h2 : 0 ≤ ∑ i ∈ s.filter (fun i => p i0 < p i), (p i - p i0) * d i := by
      refine ih _ (fun i => p i - p i0) d hs'card (fun i hi => ?_) (fun t => ?_)
      · have := (Finset.mem_filter.1 hi).2; show 0 ≤ p i - p i0; linarith
      · have hf : (s.filter (fun i => p i0 < p i)).filter (fun i => t < p i - p i0)
            = s.filter (fun i => max (t + p i0) (p i0) < p i) := by
          ext i
          simp only [Finset.mem_filter, max_lt_iff]
          constructor
          · rintro ⟨⟨hi, h1⟩, h2⟩; exact ⟨hi, by linarith, h1⟩
          · rintro ⟨hi, h1, h2⟩; exact ⟨⟨hi, h2⟩, by linarith⟩
        show 0 ≤ ∑ i ∈ (s.filter (fun i => p i0 < p i)).filter (fun i => t < p i - p i0), d i
        rw [hf]; exact h _
    rw [hsplit]; exact add_nonneg (mul_nonneg hm0 h1) h2

lemma abel_threshold' {ι : Type*} [DecidableEq ι] (s : Finset ι) (p a b : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (h : ∀ t : ℝ, ∑ i ∈ s.filter (fun i => t < p i), b i ≤ ∑ i ∈ s.filter (fun i => t < p i), a i) :
    ∑ i ∈ s, p i * b i ≤ ∑ i ∈ s, p i * a i := by
  have := abel_threshold s.card s p (fun i => a i - b i) le_rfl hp (fun t => by
    simp only [Finset.sum_sub_distrib]; linarith [h t])
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  linarith

end B170C

open MeasureTheory Set SeqPostedPricing.MatroidSPM

namespace B170C
end B170C

open MeasureTheory Set SeqPostedPricing.MatroidSPM

namespace B170C

lemma spm_zero {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (σ : Fin n ≃ Fin n) (v : Fin n → ℝ) : spmServedBefore Feas p active σ v 0 = ∅ := by
  simp [spmServedBefore]

lemma spm_succ {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (σ : Fin n ≃ Fin n) (v : Fin n → ℝ) (m : ℕ) (hm : m < n) :
    spmServedBefore Feas p active σ v (m + 1)
      = spmStep Feas p active v (spmServedBefore Feas p active σ v m) (σ ⟨m, hm⟩) := by
  unfold spmServedBefore
  rw [List.take_add_one, List.foldl_append]
  simp [hm]

lemma step_cases {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (v : Fin n → ℝ) (A : Finset (Fin n)) (x : Fin n) :
    (x ∈ active ∧ Feas (insert x A) ∧ p x ≤ v x ∧ spmStep Feas p active v A x = insert x A) ∨
    (¬ (x ∈ active ∧ Feas (insert x A) ∧ p x ≤ v x) ∧ spmStep Feas p active v A x = A) := by
  unfold spmStep
  by_cases h : x ∈ active ∧ Feas (insert x A) ∧ p x ≤ v x
  · left; exact ⟨h.1, h.2.1, h.2.2, if_pos h⟩
  · right; exact ⟨h, if_neg h⟩


lemma spm_congr {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (σ : Fin n ≃ Fin n) (v v' : Fin n → ℝ) (h : ∀ j, p j ≤ v j ↔ p j ≤ v' j) (m : ℕ) :
    spmServedBefore Feas p active σ v m = spmServedBefore Feas p active σ v' m := by
  have e : spmStep Feas p active v = spmStep Feas p active v' := by
    funext A i
    unfold spmStep
    have hi := h i
    by_cases h1 : i ∈ active ∧ Feas (insert i A) ∧ p i ≤ v i
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, hi.1 h1.2.2⟩]
    · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.1, h2.2.1, hi.2 h2.2.2⟩)]
  simp only [spmServedBefore, e]

lemma spm_meas {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (σ : Fin n ≃ Fin n) (m : ℕ) (j : Fin n) :
    MeasurableSet {v : Fin n → ℝ | j ∈ spmServedBefore Feas p active σ v m} := by
  classical
  let b : (Fin n → ℝ) → (Fin n → Bool) := fun v i => decide (p i ≤ v i)
  let w : (Fin n → Bool) → (Fin n → ℝ) := fun β i => if β i then p i else p i - 1
  have hb : Measurable b := by
    refine measurable_pi_lambda _ fun i => ?_
    refine measurable_to_countable' fun x => ?_
    cases x
    · have e : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {false} = {v | v i < p i} := by
        ext v; simp
      rw [e]; exact measurableSet_lt (measurable_pi_apply i) measurable_const
    · have e : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {true} = {v | p i ≤ v i} := by
        ext v; simp
      rw [e]; exact measurableSet_le measurable_const (measurable_pi_apply i)
  have hwb : ∀ v, ∀ i, p i ≤ v i ↔ p i ≤ w (b v) i := by
    intro v i
    by_cases h : p i ≤ v i <;> simp [w, b, h] <;> linarith
  have e : {v : Fin n → ℝ | j ∈ spmServedBefore Feas p active σ v m}
      = b ⁻¹' {β | j ∈ spmServedBefore Feas p active σ (w β) m} := by
    ext v
    simp only [mem_setOf_eq, mem_preimage]
    rw [spm_congr Feas p active σ v (w (b v)) (hwb v)]
  rw [e]
  exact hb (MeasurableSet.of_discrete)

lemma card_inter_integral {n : ℕ} (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (X : (Fin n → ℝ) → Finset (Fin n)) (hX : ∀ j, MeasurableSet {v | j ∈ X v})
    (s : Finset (Fin n)) :
    Integrable (fun v => ((X v ∩ s).card : ℝ)) P ∧
    ∫ v, ((X v ∩ s).card : ℝ) ∂P = ∑ j ∈ s, (P {v | j ∈ X v}).toReal := by
  classical
  have hf : (fun v => ((X v ∩ s).card : ℝ))
      = fun v => ∑ j ∈ s, ({v | j ∈ X v}.indicator (1 : (Fin n → ℝ) → ℝ) v) := by
    funext v
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.inter_comm]
  have hi : ∀ j, Integrable ({v | j ∈ X v}.indicator (1 : (Fin n → ℝ) → ℝ)) P :=
    fun j => (integrable_const (1 : ℝ)).indicator (hX j)
  refine ⟨?_, ?_⟩
  · rw [hf]; exact integrable_finset_sum _ (fun j _ => hi j)
  · rw [hf, integral_finset_sum _ (fun j _ => hi j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_one (hX j), measureReal_def]


lemma alloc_le_one {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (M : Mechanism n) (j : Fin n) : 0 ≤ allocProb μ M j ∧ allocProb μ M j ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold allocProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)


section Mat
variable {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
  (σ : Fin n ≃ Fin n)

lemma spm_basic (hF0 : Feas ∅) (v : Fin n → ℝ) : ∀ m : ℕ, m ≤ n →
    (∀ j ∈ spmServedBefore Feas p active σ v m, j ∈ active ∧ (σ.symm j).val < m)
    ∧ Feas (spmServedBefore Feas p active σ v m) := by
  intro m
  induction m with
  | zero => intro _; rw [spm_zero]; exact ⟨by simp, hF0⟩
  | succ m ih =>
    intro hm
    have hm' : m < n := hm
    obtain ⟨h1, h2⟩ := ih hm'.le
    rw [spm_succ _ _ _ _ _ m hm']
    rcases step_cases Feas p active v (spmServedBefore Feas p active σ v m) (σ ⟨m, hm'⟩)
      with ⟨ha, hf, _, he⟩ | ⟨_, he⟩
    · rw [he]
      refine ⟨fun j hj => ?_, hf⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact ⟨ha, by simp⟩
      · exact ⟨(h1 j hj).1, by have := (h1 j hj).2; omega⟩
    · rw [he]
      exact ⟨fun j hj => ⟨(h1 j hj).1, by have := (h1 j hj).2; omega⟩, h2⟩

lemma spm_mem (v : Fin n → ℝ) (j : Fin n) : ∀ m : ℕ, m ≤ n →
    (j ∈ spmServedBefore Feas p active σ v m ↔
      ((σ.symm j).val < m ∧ j ∈ active ∧
        Feas (insert j (spmServedBefore Feas p active σ v (σ.symm j).val)) ∧ p j ≤ v j)) := by
  intro m
  induction m with
  | zero => intro _; simp [spm_zero]
  | succ m ih =>
    intro hm
    have hm' : m < n := hm
    have ih := ih hm'.le
    rw [spm_succ _ _ _ _ _ m hm']
    by_cases hjx : j = σ ⟨m, hm'⟩
    · have hidx : (σ.symm j).val = m := by rw [hjx]; simp
      have hjS : j ∉ spmServedBefore Feas p active σ v m := by
        intro h; have := (ih.1 h).1; omega
      rw [hidx]
      rcases step_cases Feas p active v (spmServedBefore Feas p active σ v m) (σ ⟨m, hm'⟩)
        with ⟨ha, hf, hpv, he⟩ | ⟨hno, he⟩
      · rw [he]
        constructor
        · intro _
          rw [hjx]
          exact ⟨by omega, ha, hf, hpv⟩
        · intro _
          rw [hjx]; exact Finset.mem_insert_self _ _
      · rw [he]
        constructor
        · intro h; exact absurd h hjS
        · rintro ⟨_, ha, hf, hpv⟩
          rw [hjx] at ha hf hpv
          exact absurd ⟨ha, hf, hpv⟩ hno
    · have hidx : (σ.symm j).val ≠ m := by
        intro h
        apply hjx
        have : σ.symm j = ⟨m, hm'⟩ := Fin.ext h
        rw [← this, Equiv.apply_symm_apply]
      have hmem : j ∈ spmStep Feas p active v (spmServedBefore Feas p active σ v m) (σ ⟨m, hm'⟩)
          ↔ j ∈ spmServedBefore Feas p active σ v m := by
        rcases step_cases Feas p active v (spmServedBefore Feas p active σ v m) (σ ⟨m, hm'⟩)
          with ⟨_, _, _, he⟩ | ⟨_, he⟩
        · rw [he, Finset.mem_insert]
          constructor
          · rintro (h | h)
            · exact absurd h hjx
            · exact h
          · exact fun h => Or.inr h
        · rw [he]
      rw [hmem, ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma spm_congr_lt (v v' : Fin n → ℝ) : ∀ m : ℕ, m ≤ n →
    (∀ k : Fin n, k.val < m → (p (σ k) ≤ v (σ k) ↔ p (σ k) ≤ v' (σ k))) →
    spmServedBefore Feas p active σ v m = spmServedBefore Feas p active σ v' m := by
  intro m
  induction m with
  | zero => intro _ _; rw [spm_zero, spm_zero]
  | succ m ih =>
    intro hm h
    have hm' : m < n := hm
    rw [spm_succ _ _ _ _ _ m hm', spm_succ _ _ _ _ _ m hm', ih hm'.le (fun k hk => h k (by omega))]
    have hx := h ⟨m, hm'⟩ (by simp)
    unfold spmStep
    by_cases h1 : σ ⟨m, hm'⟩ ∈ active ∧
        Feas (insert (σ ⟨m, hm'⟩) (spmServedBefore Feas p active σ v' m)) ∧
        p (σ ⟨m, hm'⟩) ≤ v (σ ⟨m, hm'⟩)
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, hx.1 h1.2.2⟩]
    · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.1, h2.2.1, hx.2 h2.2.2⟩)]

lemma spm_update (v : Fin n → ℝ) (j : Fin n) (w : ℝ) :
    spmServedBefore Feas p active σ (Function.update v j w) (σ.symm j).val
      = spmServedBefore Feas p active σ v (σ.symm j).val := by
  refine spm_congr_lt Feas p active σ _ _ _ (σ.symm j).isLt.le (fun k hk => ?_)
  have hne : σ k ≠ j := by
    intro h; rw [← h, Equiv.symm_apply_apply] at hk; exact lt_irrefl _ hk
  rw [Function.update_of_ne hne]

lemma spm_meas_gen (P : Finset (Fin n) → Prop) (m : ℕ) :
    MeasurableSet {v : Fin n → ℝ | P (spmServedBefore Feas p active σ v m)} := by
  classical
  let b : (Fin n → ℝ) → (Fin n → Bool) := fun v i => decide (p i ≤ v i)
  let w : (Fin n → Bool) → (Fin n → ℝ) := fun β i => if β i then p i else p i - 1
  have hb : Measurable b := by
    refine measurable_pi_lambda _ fun i => ?_
    refine measurable_to_countable' fun x => ?_
    cases x
    · have e : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {false} = {v | v i < p i} := by
        ext v; simp
      rw [e]; exact measurableSet_lt (measurable_pi_apply i) measurable_const
    · have e : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {true} = {v | p i ≤ v i} := by
        ext v; simp
      rw [e]; exact measurableSet_le measurable_const (measurable_pi_apply i)
  have hwb : ∀ v, ∀ i, p i ≤ v i ↔ p i ≤ w (b v) i := by
    intro v i
    by_cases h : p i ≤ v i <;> simp [w, b, h] <;> linarith
  have e : {v : Fin n → ℝ | P (spmServedBefore Feas p active σ v m)}
      = b ⁻¹' {β | P (spmServedBefore Feas p active σ (w β) m)} := by
    ext v
    simp only [mem_setOf_eq, mem_preimage]
    rw [spm_congr Feas p active σ v (w (b v)) (hwb v)]
  rw [e]
  exact hb (MeasurableSet.of_discrete)

end Mat

lemma mat_card {n : ℕ} {Feas : Finset (Fin n) → Prop} (hmat : IsMatroid Feas)
    (G I B : Finset (Fin n)) (hI : Feas I) (hG : Feas G)
    (hB : ∀ j ∈ B, ¬ Feas (insert j G)) : (I ∩ B).card ≤ G.card := by
  by_contra h
  rw [not_le] at h
  obtain ⟨e, he, hfe⟩ := hmat.2 (I ∩ B) G (hmat.1 I (I ∩ B) hI Finset.inter_subset_left) hG h
  exact hB e (Finset.mem_inter.1 (Finset.mem_sdiff.1 he).1).2 hfe

lemma prob_split {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (j : Fin n)
    (E : Set (Fin n → ℝ)) (hEm : MeasurableSet E)
    (hE : ∀ v w, Function.update v j w ∈ E ↔ v ∈ E) (c : ℝ) :
    Measure.pi μ ({v | c ≤ v j} ∩ E) = Measure.pi μ E * μ j (Ici c) := by
  have hmp := update_mp μ j
  have hX : MeasurableSet ({v : Fin n → ℝ | c ≤ v j} ∩ E) :=
    (measurableSet_le measurable_const (measurable_pi_apply j)).inter hEm
  rw [← hmp.measure_preimage hX.nullMeasurableSet]
  have e : (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 j z.2) ⁻¹' ({v | c ≤ v j} ∩ E)
      = E ×ˢ Ici c := by
    ext ⟨v, w⟩
    simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, Function.update_self, mem_prod,
      mem_Ici, hE]
    exact and_comm
  rw [e, Measure.prod_prod]

section Thr
variable {n : ℕ} (Feas : Finset (Fin n) → Prop) (hmat : IsMatroid Feas) (hF0 : Feas ∅)
  (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (M : Mechanism n) (hF : ∀ v, Feas (M.alloc v))
  (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v})
  (p : Fin n → ℝ) (active : Finset (Fin n))
  (hq : ∀ j ∈ active, ((μ j) (Ici (p j))).toReal = allocProb μ M j)
  (σ : Fin n ≃ Fin n) (hσ : IsDecreasingOrder p active σ)

/-- The event that agent `j` is not blocked when its turn comes. -/
def Gd (j : Fin n) : Set (Fin n → ℝ) :=
  {v | Feas (insert j (spmServedBefore Feas p active σ v (σ.symm j).val))}

lemma Gd_meas (j : Fin n) : MeasurableSet (Gd Feas p active σ j) :=
  spm_meas_gen Feas p active σ (fun A => Feas (insert j A)) _

include hq in
lemma pr_served (j : Fin n) (hj : j ∈ active) :
    ((Measure.pi μ) {v | j ∈ spmServedBefore Feas p active σ v n}).toReal
      = allocProb μ M j * ((Measure.pi μ) (Gd Feas p active σ j)).toReal := by
  have e : {v | j ∈ spmServedBefore Feas p active σ v n}
      = {v | p j ≤ v j} ∩ Gd Feas p active σ j := by
    ext v
    simp only [mem_setOf_eq, mem_inter_iff, Gd]
    rw [spm_mem Feas p active σ v j n le_rfl]
    constructor
    · rintro ⟨_, _, hf, hpv⟩; exact ⟨hpv, hf⟩
    · rintro ⟨hpv, hf⟩; exact ⟨(σ.symm j).isLt, hj, hf, hpv⟩
  rw [e, prob_split μ j _ (Gd_meas Feas p active σ j) (fun v w => by
      simp only [Gd, mem_setOf_eq]; rw [spm_update]) (p j),
    ENNReal.toReal_mul, hq j hj, mul_comm]

include hmat hF0 hF hmeas hσ in
lemma pointwise_block (t : ℝ) (v : Fin n → ℝ) :
    ∑ j ∈ active.filter (fun j => t < p j),
        allocProb μ M j * (1 - (Gd Feas p active σ j).indicator (1 : (Fin n → ℝ) → ℝ) v)
      ≤ ((spmServedBefore Feas p active σ v n ∩ active.filter (fun j => t < p j)).card : ℝ) := by
  classical
  set T := active.filter (fun j => t < p j) with hT
  set B := T.filter (fun j => v ∉ Gd Feas p active σ j) with hB
  set G := spmServedBefore Feas p active σ v n ∩ T with hG
  have e1 : ∑ j ∈ T, allocProb μ M j * (1 - (Gd Feas p active σ j).indicator (1 : (Fin n → ℝ) → ℝ) v)
      = ∑ j ∈ B, allocProb μ M j := by
    have e1' : ∑ j ∈ B, allocProb μ M j
        = ∑ j ∈ T, if v ∉ Gd Feas p active σ j then allocProb μ M j else 0 := Finset.sum_filter _ _
    rw [e1']
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : v ∈ Gd Feas p active σ j
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [e1]
  have hGf : Feas G :=
    hmat.1 _ _ (spm_basic Feas p active σ hF0 v n le_rfl).2 Finset.inter_subset_left
  have hBb : ∀ j ∈ B, ¬ Feas (insert j G) := by
    intro j hjB hfe
    have hjB' := Finset.mem_filter.1 hjB
    have hjT := Finset.mem_filter.1 hjB'.1
    apply hjB'.2
    show Feas (insert j (spmServedBefore Feas p active σ v (σ.symm j).val))
    refine hmat.1 _ _ hfe (Finset.insert_subset_insert j ?_)
    intro k hk
    have hk' := (spm_mem Feas p active σ v k _ (σ.symm j).isLt.le).1 hk
    have hkn : k ∈ spmServedBefore Feas p active σ v n :=
      (spm_mem Feas p active σ v k n le_rfl).2 ⟨(σ.symm k).isLt, hk'.2⟩
    have hle : p j ≤ p k := by
      have := hσ (σ.symm k) (σ.symm j) (Fin.le_iff_val_le_val.2 hk'.1.le)
        (by rw [Equiv.apply_symm_apply]; exact hk'.2.1)
        (by rw [Equiv.apply_symm_apply]; exact hjT.1)
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact Finset.mem_inter.2 ⟨hkn, Finset.mem_filter.2 ⟨hk'.2.1, by linarith [hjT.2]⟩⟩
  obtain ⟨hAi, hAe⟩ := card_inter_integral (Measure.pi μ) M.alloc hmeas B
  have h2 : ∫ w, ((M.alloc w ∩ B).card : ℝ) ∂(Measure.pi μ)
      ≤ ∫ w, (G.card : ℝ) ∂(Measure.pi μ) := by
    refine integral_mono hAi (integrable_const _) fun w => ?_
    show ((M.alloc w ∩ B).card : ℝ) ≤ (G.card : ℝ)
    exact Nat.cast_le.2 (mat_card hmat G (M.alloc w) B (hF w) hGf hBb)
  rw [hAe] at h2
  simp only [integral_const, probReal_univ, one_smul] at h2
  exact h2

include hmat hF0 hF hmeas hq hσ in
lemma thr_mat (t : ℝ) :
    ∑ j ∈ active.filter (fun j => t < p j), (1 / 2 : ℝ) * allocProb μ M j
      ≤ ∑ j ∈ active.filter (fun j => t < p j),
          ((Measure.pi μ) {v | j ∈ spmServedBefore Feas p active σ v n}).toReal := by
  set T := active.filter (fun j => t < p j) with hT
  have hTa : ∀ j ∈ T, j ∈ active := fun j hj => (Finset.mem_filter.1 hj).1
  have hind : ∀ j, Integrable ((Gd Feas p active σ j).indicator (1 : (Fin n → ℝ) → ℝ))
      (Measure.pi μ) := fun j => (integrable_const (1 : ℝ)).indicator (Gd_meas Feas p active σ j)
  have hfi : ∀ j, Integrable (fun v => allocProb μ M j *
      (1 - (Gd Feas p active σ j).indicator (1 : (Fin n → ℝ) → ℝ) v)) (Measure.pi μ) :=
    fun j => ((integrable_const 1).sub (hind j)).const_mul _
  obtain ⟨hSi, hSe⟩ := card_inter_integral (Measure.pi μ)
    (fun v => spmServedBefore Feas p active σ v n) (fun j => spm_meas _ _ _ _ _ j) T
  have hmono := integral_mono (integrable_finset_sum _ (fun j _ => hfi j)) hSi
    (fun v => pointwise_block Feas hmat hF0 μ M hF hmeas p active σ hσ t v)
  rw [hSe, integral_finset_sum _ (fun j _ => hfi j)] at hmono
  have hcomp : ∀ j, ∫ v, allocProb μ M j *
      (1 - (Gd Feas p active σ j).indicator (1 : (Fin n → ℝ) → ℝ) v) ∂(Measure.pi μ)
      = allocProb μ M j * (1 - ((Measure.pi μ) (Gd Feas p active σ j)).toReal) := by
    intro j
    rw [integral_const_mul, integral_sub (integrable_const 1) (hind j),
      integral_indicator_one (Gd_meas Feas p active σ j), measureReal_def]
    simp
  simp only [hcomp] at hmono
  have hpr : ∑ j ∈ T, ((Measure.pi μ) {v | j ∈ spmServedBefore Feas p active σ v n}).toReal
      = ∑ j ∈ T, allocProb μ M j * ((Measure.pi μ) (Gd Feas p active σ j)).toReal :=
    Finset.sum_congr rfl fun j hj => pr_served Feas μ M p active hq σ j (hTa j hj)
  rw [hpr] at hmono ⊢
  have hs : ∑ j ∈ T, allocProb μ M j * (1 - ((Measure.pi μ) (Gd Feas p active σ j)).toReal)
      = ∑ j ∈ T, allocProb μ M j
        - ∑ j ∈ T, allocProb μ M j * ((Measure.pi μ) (Gd Feas p active σ j)).toReal := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs] at hmono
  rw [← Finset.mul_sum]
  linarith

end Thr

end B170C

open B170C

open MeasureTheory Set SeqPostedPricing.MatroidSPM in
theorem solution {n : ℕ} (Feas : Finset (Fin n) → Prop) (hmat : IsMatroid Feas)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (hreg : ∀ i, IsRegular (μ i))
    (M : Mechanism n) (hM : IsOptimal Feas μ M)
    (p : Fin n → ℝ) (hp : ∀ i ∈ spmActive μ M, IsQuantilePrice (μ i) (allocProb μ M i) (p i))
    (σ : Fin n ≃ Fin n) (hσ : IsDecreasingOrder p (spmActive μ M) σ) :
    revenue μ M ≤ 2 * spmRevenue Feas μ p (spmActive μ M) σ := by
  classical
  have hM' := hM
  obtain ⟨⟨hF, hT, hIR, hmeas, hint⟩, -⟩ := hM'
  have hmem : ∀ i, i ∈ spmActive μ M ↔ 0 < allocProb μ M i := fun i => by
    simp [spmActive]
  have hatom : ∀ i x, (μ i) {x} = 0 := by
    intro i x
    obtain ⟨f, _, _, hν, _⟩ := hreg i
    rw [hν, withDensity_apply _ (measurableSet_singleton x),
      Measure.restrict_eq_zero.2 Real.volume_singleton]
    simp
  have hqI : ∀ j ∈ spmActive μ M, ((μ j) (Ici (p j))).toReal = allocProb μ M j := fun j hj => by
    rw [measure_congr (Ioi_ae_eq_Ici' (hatom j (p j))).symm]
    exact (hp j hj).1
  have hpay : ∀ i, ∫ v, M.pay v i ∂(Measure.pi μ)
      ≤ if i ∈ spmActive μ M then p i * allocProb μ M i else 0 := by
    intro i
    by_cases hi : i ∈ spmActive μ M
    · rw [if_pos hi]
      have hqi := (hmem i).1 hi
      rcases (alloc_le_one μ M i).2.lt_or_eq with hlt | heq
      · obtain ⟨c, hc, hK⟩ := keyK (μ i) (hreg i) (p i) (by rw [(hp i hi).1]; exact hqi)
          (by rw [(hp i hi).1]; exact hlt)
        have h1 := pay_bound_interior μ M hT hIR hmeas hint i c
          ((p i - c) * ((μ i) (Ioi (p i))).toReal) (fun θ _ => hK θ)
          (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
        rw [(hp i hi).1] at h1
        linarith [show c * allocProb μ M i + (p i - c) * allocProb μ M i = p i * allocProb μ M i by ring]
      · have h1 := pay_bound_full μ M hT hIR hmeas hint i heq (p i)
          (fun p' hp' => by have h2 := (hp i hi).2 p' hp'; rwa [heq] at h2)
        rw [heq, mul_one]; exact h1
    · rw [if_neg hi]
      have h0 : allocProb μ M i = 0 :=
        le_antisymm (not_lt.1 (fun h => hi ((hmem i).2 h))) (alloc_le_one μ M i).1
      exact pay_bound_zero μ M hIR hmeas i h0
  have hdown : ∀ (S : Finset (Fin n)) (i : Fin n), Feas S → Feas (S.erase i) :=
    fun S i h => hmat.1 S _ h (Finset.erase_subset i S)
  have hF0 : Feas ∅ := hmat.1 _ ∅ (hF 0) (Finset.empty_subset _)
  have hp0 : ∀ i ∈ spmActive μ M, 0 ≤ p i := by
    intro i hi
    have h1 := pay_nonneg μ M hM hdown i
    have h2 := hpay i
    rw [if_pos hi] at h2
    have hqi := (hmem i).1 hi
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) hqi
    linarith
  have hrev : revenue μ M ≤ ∑ i ∈ spmActive μ M, p i * allocProb μ M i := by
    unfold revenue
    rw [integral_finset_sum _ (fun i _ => hint i)]
    calc ∑ i, ∫ v, M.pay v i ∂(Measure.pi μ)
        ≤ ∑ i, (if i ∈ spmActive μ M then p i * allocProb μ M i else 0) :=
          Finset.sum_le_sum fun i _ => hpay i
      _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hSa : ∀ v, spmServedBefore Feas p (spmActive μ M) σ v n ⊆ spmActive μ M :=
    fun v j hj => ((spm_basic Feas p (spmActive μ M) σ hF0 v n le_rfl).1 j hj).1
  have hspm : spmRevenue Feas μ p (spmActive μ M) σ
      = ∑ i ∈ spmActive μ M, p i * ((Measure.pi μ)
          {v | i ∈ spmServedBefore Feas p (spmActive μ M) σ v n}).toReal := by
    unfold spmRevenue
    have e : (fun v => ∑ i ∈ spmServedBefore Feas p (spmActive μ M) σ v n, p i)
        = fun v => ∑ i ∈ spmActive μ M,
          {v | i ∈ spmServedBefore Feas p (spmActive μ M) σ v n}.indicator
            (fun _ => p i) v := by
      funext v
      simp only [Set.indicator, Set.mem_setOf_eq]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hSa v)]
    rw [e, integral_finset_sum _ (fun i _ => (integrable_const (p i)).indicator (spm_meas _ _ _ _ _ i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (spm_meas _ _ _ _ _ i), measureReal_def, smul_eq_mul, mul_comm]
  have habel := abel_threshold' (spmActive μ M) p
    (fun i => ((Measure.pi μ)
      {v | i ∈ spmServedBefore Feas p (spmActive μ M) σ v n}).toReal)
    (fun i => (1 / 2 : ℝ) * allocProb μ M i) hp0
    (fun t => thr_mat Feas hmat hF0 μ M hF hmeas p (spmActive μ M) hqI σ hσ t)
  have hsum : ∑ i ∈ spmActive μ M, p i * ((1 / 2 : ℝ) * allocProb μ M i)
      = (1 / 2 : ℝ) * ∑ i ∈ spmActive μ M, p i * allocProb μ M i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hspm]
  linarith
