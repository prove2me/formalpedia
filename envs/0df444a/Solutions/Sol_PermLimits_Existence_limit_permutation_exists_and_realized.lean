-- Prove2me | solution 1 for PermLimits.Existence.limit_permutation_exists_and_realized
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T06:29:24.018884+00:00
-- url     : https://prove2.me/submissions/c214d962-2fc1-4711-a301-1b9e7e542362

-- Licensed under Apache 2.0. Complete permutation-limit existence and realization theorem.
import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
open PermLimits.Shared


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared

def UniformMarginals (μ : ProbabilityMeasure (I × I)) : Prop :=
  (μ : Measure (I × I)).map Prod.fst = volume ∧
  (μ : Measure (I × I)).map Prod.snd = volume

def patternProbability {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (τ : Equiv.Perm (Fin k)) : ℝ :=
  (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (patternEvent τ)

def gridPoint {n : ℕ} (i : Fin n) : I :=
  ⟨((i.val : ℝ) + 1) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
    constructor
    · positivity
    · apply (div_le_one hn).2
      exact_mod_cast i.isLt⟩

def empiricalLaw {n : ℕ} (π : Equiv.Perm (Fin n)) : ProbabilityMeasure (I × I) := by
  classical
  by_cases hn : 0 < n
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let ν : ProbabilityMeasure (Fin n) := ⟨(PMF.uniformOfFintype (Fin n)).toMeasure,
      inferInstance⟩
    exact ν.map (measurable_of_finite (fun i => (gridPoint i, gridPoint (π i)))).aemeasurable
  · exact ⟨Measure.dirac (0, 0), inferInstance⟩

end PermutationLimitProof


namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set

lemma quantile_threshold {Z : I → I → ℝ} {x u : I}
    (hF : IsCDF (Z x)) : (u : ℝ) ≤ Z x (quantile Z x u) := by
  let S : Set I := {y | (u : ℝ) ≤ Z x y}
  have hne : S.Nonempty := ⟨1, by simpa [S, hF.2.2.2] using u.2.2⟩
  have hsub : S ⊆ Ici (sInf S) := fun y hy => sInf_le hy
  have hc : ContinuousWithinAt (Z x) S (sInf S) := (hF.2.1 _).mono hsub
  have hm : MapsTo (Z x) S (Ici (u : ℝ)) := fun _ hy => hy
  have hh := hc.mem_closure (sInf_mem_closure hne) hm
  rw [isClosed_Ici.closure_eq] at hh
  exact hh

lemma quantile_le_iff {Z : I → I → ℝ} {x u y : I}
    (hF : IsCDF (Z x)) : quantile Z x u ≤ y ↔ (u : ℝ) ≤ Z x y := by
  constructor
  · intro h
    exact (quantile_threshold hF).trans (hF.1 h)
  · intro h
    exact sInf_le h

lemma quantile_zero {Z : I → I → ℝ} {x : I} (hF : IsCDF (Z x)) :
    quantile Z x 0 = 0 := by
  apply le_antisymm
  · exact (quantile_le_iff hF).mpr hF.2.2.1
  · exact bot_le

end PermutationLimitProof


namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set Filter Topology

lemma limitPerm_integrable {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    Integrable (Function.uncurry Z) (volume : Measure (I × I)) := by
  apply (integrable_const (1 : ℝ)).mono' hZ.1.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖Z p.1 p.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hZ.2.1 p.1 p.2).1]
    exact (hZ.2.1 p.1 p.2).2

lemma good_points_approach {P : I → Prop} (hP : ∀ᵐ y : I, P y)
    {y : I} (hy : y < 1) :
    ∃ z : ℕ → I, (∀ j, y < z j ∧ P (z j)) ∧ Tendsto z atTop (𝓝 y) := by
  let b (j : ℕ) : I := ⟨min 1 ((y : ℝ)+1/((j : ℝ)+1)), by
    constructor
    · apply le_min (by norm_num)
      exact add_nonneg y.2.1 (by positivity)
    · exact min_le_left _ _⟩
  have hb (j : ℕ) : y < b j := by
    change (y : ℝ) < min 1 ((y : ℝ)+1/((j : ℝ)+1))
    exact lt_min (show (y : ℝ)<1 from hy) (lt_add_of_pos_right _ (by positivity))
  have hex (j : ℕ) : ∃ z : I, z ∈ Ioo y (b j) ∧ P z := by
    apply Measure.exists_mem_of_measure_ne_zero_of_ae
    · rw [unitInterval.volume_Ioo]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hb j)))
    · exact ae_restrict_of_ae hP
  choose z hz using hex
  refine ⟨z, fun j => ⟨(hz j).1.1, (hz j).2⟩, ?_⟩
  apply tendsto_subtype_rng.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun j : ℕ => (y : ℝ)+1/((j : ℝ)+1)) atTop (𝓝 (y : ℝ)) by
      simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  · intro j
    exact (hz j).1.1.le
  · intro j
    exact (show (z j : ℝ)<(b j : ℝ) from (hz j).1.2).le.trans (min_le_right _ _)

lemma horizontal_aemeasurable {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (y : I) :
    AEMeasurable (fun x => Z x y) (volume : Measure I) := by
  by_cases hy : y=1
  · have he : (fun x => Z x y) = fun _ => (1 : ℝ) := by
      funext x
      simpa [hy] using (hZ.2.2.1 x).2.2.2
    rw [he]
    exact aemeasurable_const
  have hgood : ∀ᵐ y : I, Integrable (fun x => Z x y) :=
    (limitPerm_integrable hZ).prod_left_ae
  obtain ⟨z, hz, hlim⟩ := good_points_approach hgood (lt_of_le_of_ne (le_top : y≤1) hy)
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun j => (hz j).2.aemeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hseq : Tendsto z atTop (𝓝[Ici y] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall fun j => (hz j).1.le⟩
  exact (show Tendsto (Z x) (𝓝[Ici y] y) (𝓝 (Z x y)) from (hZ.2.2.1 x).2.1 y).comp hseq

lemma horizontal_integrable {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (y : I) :
    Integrable (fun x => Z x y) (volume : Measure I) := by
  apply (integrable_const (1 : ℝ)).mono' (horizontal_aemeasurable hZ y).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hZ.2.1 x y).1]
    exact (hZ.2.1 x y).2

end PermutationLimitProof


namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set Filter Topology

abbrev RationalUnit := {q : ℚ // 0≤q ∧ q≤1}

def rationalPoint (q : RationalUnit) : I :=
  ⟨(q.val : ℝ), by
    change 0≤(q.val : ℝ) ∧ (q.val : ℝ)≤1
    exact_mod_cast q.property⟩

lemma quantile_rational_inf {Z : I → I → ℝ} {x u : I} (hF : IsCDF (Z x)) :
    quantile Z x u = ⨅ q : RationalUnit,
      if (u : ℝ) ≤ Z x (rationalPoint q) then rationalPoint q else 1 := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro q
    split_ifs with h
    · exact (quantile_le_iff hF).mpr h
    · exact le_top
  · by_contra hh
    have hh' : quantile Z x u < ⨅ q : RationalUnit,
        if (u : ℝ) ≤ Z x (rationalPoint q) then rationalPoint q else 1 := lt_of_not_ge hh
    obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn
      (show (quantile Z x u : ℝ) < (↑(⨅ q : RationalUnit,
        if (u : ℝ) ≤ Z x (rationalPoint q) then rationalPoint q else 1) : ℝ) from hh')
    have hri : 0≤r ∧ r≤1 := by
      constructor
      · exact_mod_cast (show (0 : ℝ)≤r from (quantile Z x u).2.1.trans hr0.le)
      · exact_mod_cast (show (r : ℝ)≤1 from hr1.le.trans ((⨅ q : RationalUnit,
          if (u : ℝ) ≤ Z x (rationalPoint q) then rationalPoint q else 1) : I).2.2)
    let q : RationalUnit := ⟨r, hri⟩
    have hq : (u : ℝ) ≤ Z x (rationalPoint q) :=
      (quantile_le_iff hF).mp hr0.le
    have hb := iInf_le (fun q : RationalUnit =>
      if (u : ℝ) ≤ Z x (rationalPoint q) then rationalPoint q else 1) q
    rw [if_pos hq] at hb
    exact (not_le_of_gt hr1) hb

open Classical in
lemma aemeasurable_ite_constants {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {S : Set α} (hS : NullMeasurableSet S μ) (a b : β) :
    AEMeasurable (fun x => if x∈S then a else b) μ := by
  classical
  have hm : Measurable (fun x => if x∈toMeasurable μ S then a else b) :=
    Measurable.ite (measurableSet_toMeasurable μ S) measurable_const measurable_const
  apply hm.aemeasurable.congr
  filter_upwards [hS.toMeasurable_ae_eq.mem_iff] with x hx
  simp only [hx]

lemma quantile_aemeasurable {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    AEMeasurable (fun p : I × I => quantile Z p.1 p.2) volume := by
  classical
  have hf (q : RationalUnit) :
      AEMeasurable (fun p : I × I =>
        if (p.2 : ℝ)≤Z p.1 (rationalPoint q) then rationalPoint q else 1) volume := by
    apply aemeasurable_ite_constants
    apply nullMeasurableSet_le (measurable_snd.subtype_val.aemeasurable)
    exact (horizontal_aemeasurable hZ (rationalPoint q)).comp_quasiMeasurePreserving
      measurePreserving_fst.quasiMeasurePreserving
  have he : (fun p : I × I => quantile Z p.1 p.2) = fun p =>
      ⨅ q : RationalUnit, if (p.2 : ℝ)≤Z p.1 (rationalPoint q) then rationalPoint q else 1 := by
    funext p
    exact quantile_rational_inf (hZ.2.2.1 p.1)
  rw [he]
  exact AEMeasurable.iInf hf

lemma quantile_map_aemeasurable {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    AEMeasurable (fun p : I × I => (p.1, quantile Z p.1 p.2)) volume :=
  measurable_fst.aemeasurable.prodMk (quantile_aemeasurable hZ)

end PermutationLimitProof


namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set Filter Topology

lemma limitMeasure_probability {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    IsProbabilityMeasure (limitMeasure Z) :=
  Measure.isProbabilityMeasure_map (quantile_map_aemeasurable hZ)

lemma interval_indicator_integral (a : I) :
    (∫ u : I, if (u : ℝ)≤a then (1 : ℝ) else 0) = (a : ℝ) := by
  have he : (fun u : I => if (u : ℝ)≤a then (1 : ℝ) else 0) =
      (Iic a).indicator 1 := by
    funext u
    rfl
  rw [he, integral_indicator_one measurableSet_Iic, measureReal_def, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal a.2.1]

lemma limitMeasure_rectangle {Z : I → I → ℝ} (hZ : IsLimitPerm Z)
    {B : Set I} (hB : MeasurableSet B) (y : I) :
    (limitMeasure Z).real (B ×ˢ Iic y) = ∫ x in B, Z x y := by
  classical
  let T : I × I → I × I := fun p => (p.1, quantile Z p.1 p.2)
  let f : I × I → ℝ := (B ×ˢ Iic y).indicator 1
  have hf : Measurable f := measurable_const.indicator (hB.prod measurableSet_Iic)
  have hT : AEMeasurable T volume := quantile_map_aemeasurable hZ
  have hfi : Integrable (fun p => f (T p)) (volume : Measure (I × I)) := by
    apply (integrable_const (1 : ℝ)).mono' (hf.comp_aemeasurable hT).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖(B ×ˢ Iic y).indicator (fun _ => (1 : ℝ)) (T p)‖ ≤ 1
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
  have hinner (x : I) : (∫ u : I, f (T (x,u))) = if x∈B then Z x y else 0 := by
    have he : (fun u : I => f (T (x,u))) = fun u : I =>
        if x∈B then (if (u : ℝ)≤Z x y then (1 : ℝ) else 0) else 0 := by
      funext u
      simp only [f, T, Set.indicator_apply, mem_prod, mem_Iic, Pi.one_apply,
        quantile_le_iff (hZ.2.2.1 x)]
      split_ifs <;> simp_all
    rw [he]
    by_cases hx : x∈B
    · simp only [if_pos hx]
      exact interval_indicator_integral ⟨Z x y, hZ.2.1 x y⟩
    · simp [hx]
  calc
    _ = ∫ p, f p ∂limitMeasure Z := (integral_indicator_one (hB.prod measurableSet_Iic)).symm
    _ = ∫ p, f (T p) := integral_map hT hf.aestronglyMeasurable
    _ = ∫ x : I, ∫ u : I, f (T (x,u)) := integral_prod _ hfi
    _ = ∫ x : I, if x∈B then Z x y else 0 := by simp only [hinner]
    _ = ∫ x in B, Z x y := integral_indicator hB

noncomputable def nativeLaw (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    ProbabilityMeasure (I × I) := ⟨limitMeasure Z, limitMeasure_probability hZ⟩

lemma nativeLaw_uniform {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    UniformMarginals (nativeLaw Z hZ) := by
  have := limitMeasure_probability hZ
  constructor
  · apply Measure.ext_of_Iic
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change ((limitMeasure Z).map Prod.fst).real (Iic x) = volume.real (Iic x)
    have he : Prod.fst ⁻¹' Iic x = Iic x ×ˢ Iic (1 : I) := by
      ext p
      change p.1≤x ↔ p.1≤x ∧ p.2≤1
      simp only [show p.2≤(1 : I) from le_top, and_true]
    rw [measureReal_def, Measure.map_apply measurable_fst measurableSet_Iic, he,
      ← measureReal_def, limitMeasure_rectangle hZ measurableSet_Iic 1]
    have hf : (fun t : I => Z t 1) = fun _ => (1 : ℝ) := by
      funext t
      exact (hZ.2.2.1 t).2.2.2
    rw [hf, setIntegral_one_eq_measureReal]
  · apply Measure.ext_of_Iic
    intro y
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change ((limitMeasure Z).map Prod.snd).real (Iic y) = volume.real (Iic y)
    have he : Prod.snd ⁻¹' Iic y = (univ : Set I) ×ˢ Iic y := by ext p; simp
    rw [measureReal_def, Measure.map_apply measurable_snd measurableSet_Iic, he,
      ← measureReal_def, limitMeasure_rectangle hZ MeasurableSet.univ y, setIntegral_univ,
      hZ.2.2.2 y, measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal y.2.1]

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval Set PermLimits.Shared

def kernelCDF (κ : Kernel I I) (x y : I) : ℝ := (κ x).real (Iic y)

lemma kernelCDF_isCDF (κ : Kernel I I) [IsMarkovKernel κ] (x : I) :
    IsCDF (kernelCDF κ x) := by
  have he (y : I) : kernelCDF κ x y = cdf ((κ x).map Subtype.val) (y : ℝ) := by
    rw [unitInterval.cdf_eq_real]
    have hs : Iic y = Icc (0 : I) y := by ext z; simp
    simp only [kernelCDF, hs]
  refine ⟨?_, ?_, measureReal_nonneg, ?_⟩
  · intro y z hyz
    exact measureReal_mono (Iic_subset_Iic.mpr hyz)
  · intro y
    rw [show kernelCDF κ x = (fun y : I => cdf ((κ x).map Subtype.val) (y : ℝ)) from funext he]
    exact (cdf ((κ x).map Subtype.val)).right_continuous (y : ℝ) |>.comp
      continuous_subtype_val.continuousWithinAt (fun z hz => hz)
  · change (κ x).real (Iic (⊤ : I)) = 1
    simp

lemma kernelCDF_bounds (κ : Kernel I I) [IsMarkovKernel κ] (x y : I) :
    kernelCDF κ x y ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

lemma kernelCDF_measurable (κ : Kernel I I) [IsMarkovKernel κ] :
    Measurable (Function.uncurry (kernelCDF κ)) := by
  let η : Kernel (I × I) I := κ.comap Prod.fst measurable_fst
  have hm : Measurable (fun p : (I × I) × I =>
      if p.2 ≤ p.1.2 then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
      measurable_const measurable_const
  have hi := hm.stronglyMeasurable.integral_kernel_prod_right (κ := η)
    (f := fun p z => if z ≤ p.2 then (1 : ℝ) else 0)
  have he : (fun p : I × I => ∫ z, (if z ≤ p.2 then (1 : ℝ) else 0) ∂η p) =
      Function.uncurry (kernelCDF κ) := by
    funext p
    change (∫ z, (Iic p.2).indicator (fun _ => (1 : ℝ)) z ∂κ p.1) = _
    rw [integral_indicator measurableSet_Iic]
    change (∫ z in Iic p.2, (1 : ℝ) ∂κ p.1) = (κ p.1).real (Iic p.2)
    simp
  rw [he] at hi
  exact hi.measurable

lemma kernelCDF_rectangle (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {B : Set I} (hB : MeasurableSet B) (y : I) :
    ∫ x in B, kernelCDF (μ : Measure (I × I)).condKernel x y =
      (μ : Measure (I × I)).real (B ×ˢ Iic y) := by
  have hf : (μ : Measure (I × I)).fst = volume := hμ.1
  have h := Measure.setIntegral_condKernel (ρ := (μ : Measure (I × I)))
    (f := fun _ => (1 : ℝ)) (t := Iic y) hB measurableSet_Iic (integrable_const _).integrableOn
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [hf] at h
  simpa only [kernelCDF, Measure.real, Measure.restrict_apply_univ] using h

lemma kernelCDF_isLimitPerm (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ) :
    IsLimitPerm (kernelCDF (μ : Measure (I × I)).condKernel) := by
  refine ⟨(kernelCDF_measurable _).aemeasurable, kernelCDF_bounds _, kernelCDF_isCDF _, ?_⟩
  intro y
  have h := kernelCDF_rectangle μ hμ MeasurableSet.univ y
  simp only [Measure.restrict_univ] at h
  rw [h]
  have hy := congrArg (fun ν : Measure I => ν.real (Iic y)) hμ.2
  rw [map_measureReal_apply measurable_snd measurableSet_Iic] at hy
  have hs : Prod.snd ⁻¹' Iic y = (univ : Set I) ×ˢ Iic y := by ext z; simp
  simpa [hs, unitInterval.volume_Iic, Measure.real, y.2.1] using hy

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set

def rectangleSection (μ : Measure (I × I)) (B : Set I) : Measure I :=
  (μ.restrict (B ×ˢ univ)).map Prod.snd

lemma rectangleSection_apply (μ : Measure (I × I)) (B C : Set I)
    (hC : MeasurableSet C) : rectangleSection μ B C = μ (B ×ˢ C) := by
  rw [rectangleSection, Measure.map_apply measurable_snd hC,
    Measure.restrict_apply (hC.preimage measurable_snd)]
  congr 1
  ext p
  simp [and_comm]

lemma measure_eq_of_lower_rectangles (μ ν : Measure (I × I)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ (B : Set I), MeasurableSet B → ∀ y : I, μ.real (B ×ˢ Iic y) = ν.real (B ×ˢ Iic y)) :
    μ = ν := by
  apply Measure.ext_prod
  intro B C hB hC
  have : IsFiniteMeasure (rectangleSection μ B) := by unfold rectangleSection; infer_instance
  have he : rectangleSection μ B = rectangleSection ν B := by
    apply Measure.ext_of_Iic
    intro y
    rw [rectangleSection_apply _ _ _ measurableSet_Iic,
      rectangleSection_apply _ _ _ measurableSet_Iic]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (h B hB y)
  have he' := congrArg (fun ξ : Measure I => ξ C) he
  simpa only [rectangleSection_apply _ _ _ hC] using he'

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared

lemma law_representation (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ) :
    ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ limitMeasure Z = (μ : Measure (I × I)) := by
  let Z := kernelCDF (μ : Measure (I × I)).condKernel
  have hZ : IsLimitPerm Z := kernelCDF_isLimitPerm μ hμ
  refine ⟨Z, hZ, ?_⟩
  have : IsProbabilityMeasure (limitMeasure Z) := limitMeasure_probability hZ
  apply measure_eq_of_lower_rectangles
  intro B hB y
  rw [limitMeasure_rectangle hZ hB y]
  exact kernelCDF_rectangle μ hμ hB y

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set
open scoped ENNReal

def gridLeft {n : ℕ} (i : Fin n) : I :=
  ⟨(i.val : ℝ) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
    exact ⟨by positivity, (div_le_one hn).2 (by exact_mod_cast i.isLt.le)⟩⟩

def gridCell {n : ℕ} (i : Fin n) : Set I := Ioc (gridLeft i) (gridPoint i)

lemma gridCell_measurable {n : ℕ} (i : Fin n) : MeasurableSet (gridCell i) := measurableSet_Ioc

lemma mem_gridCell {n : ℕ} (i : Fin n) (x : I) :
    x ∈ gridCell i ↔ (i.val : ℝ) / n < x ∧ (x : ℝ) ≤ ((i.val : ℝ) + 1) / n := Iff.rfl

lemma gridCell_volume {n : ℕ} (i : Fin n) : volume (gridCell i) = (n : ℝ≥0∞)⁻¹ := by
  rw [gridCell, unitInterval.volume_Ioc]
  change ENNReal.ofReal (((i.val : ℝ) + 1) / n - (i.val : ℝ) / n) = _
  have he : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = (n : ℝ)⁻¹ := by ring
  rw [he, ENNReal.ofReal_inv_of_pos (by exact_mod_cast i.pos)]
  simp

lemma gridCell_disjoint {n : ℕ} : Pairwise (fun i j : Fin n => Disjoint (gridCell i) (gridCell j)) := by
  intro i j hij
  wlog h : i < j generalizing i j
  · exact (@this j i hij.symm (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij))).symm
  apply Set.disjoint_left.2
  intro x hxi hxj
  rw [mem_gridCell] at hxi hxj
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
  have hd := div_le_div_of_nonneg_right hij' hn.le
  exact (not_lt_of_ge (hxi.2.trans hd)) hxj.1

lemma gridCell_cover {n : ℕ} (hn : 0 < n) :
    (⋃ i : Fin n, gridCell i) = Ioi (0 : I) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
    have h := (mem_gridCell i x).1 hxi
    have hz : (0 : ℝ) ≤ (i.val : ℝ) / n := by positivity
    exact hz.trans_lt h.1
  · intro hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hx' : (x : ℝ) ∈ Ioc ((0 : ℝ) / n) ((n : ℝ) / n) := by
      simpa [hn'.ne'] using (show (0 : ℝ) < x ∧ (x : ℝ) ≤ 1 from ⟨hx, x.2.2⟩)
    have h := Ioc_subset_biUnion_Ioc n (fun j : ℕ => (j : ℝ) / n) (by simpa only [Nat.cast_zero] using hx')
    simp only [mem_iUnion, Finset.mem_range] at h
    obtain ⟨j, hj, hxj⟩ := h
    refine mem_iUnion.2 ⟨⟨j, hj⟩, ?_⟩
    simpa only [mem_gridCell, Set.mem_Ioc, Nat.cast_add, Nat.cast_one] using hxj

lemma gridCell_diameter {n : ℕ} (i : Fin n) {x y : I}
    (hx : x ∈ gridCell i) (hy : y ∈ gridCell i) : dist x y ≤ (n : ℝ)⁻¹ := by
  rw [mem_gridCell] at hx hy
  change |(x : ℝ) - y| ≤ _
  rw [abs_le]
  have he : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = (n : ℝ)⁻¹ := by ring
  constructor <;> linarith

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set Filter

lemma volume_ae_pos : ∀ᵐ x : I, 0 < x := by
  rw [ae_iff]
  have hs : {a : I | ¬0 < a} = Iic (0 : I) := by ext a; simp
  rw [hs, unitInterval.volume_Iic]
  norm_num

lemma uniform_ae_pos (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ) :
    ∀ᵐ p ∂(μ : Measure (I × I)), 0 < p.1 ∧ 0 < p.2 := by
  have hx : ∀ᵐ p ∂(μ : Measure (I × I)), 0 < p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hμ.1]
    exact volume_ae_pos
  have hy : ∀ᵐ p ∂(μ : Measure (I × I)), 0 < p.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hμ.2]
    exact volume_ae_pos
  exact hx.and hy

lemma grid_square_cover (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) :
    ∀ᵐ p ∂(μ : Measure (I × I)), ∃ j : Fin n × Fin n,
      p ∈ gridCell j.1 ×ˢ gridCell j.2 := by
  filter_upwards [uniform_ae_pos μ hμ] with p hp
  have hx : p.1 ∈ ⋃ i : Fin n, gridCell i := by rw [gridCell_cover hn]; exact hp.1
  have hy : p.2 ∈ ⋃ i : Fin n, gridCell i := by rw [gridCell_cover hn]; exact hp.2
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨j, hj⟩ := mem_iUnion.1 hy
  exact ⟨(i,j), hi, hj⟩

lemma grid_square_disjoint {n : ℕ} : Pairwise (fun i j : Fin n × Fin n =>
    Disjoint (gridCell i.1 ×ˢ gridCell i.2) (gridCell j.1 ×ˢ gridCell j.2)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro p hpi hpj
  by_cases h : i.1 = j.1
  · have h' : i.2 ≠ j.2 := fun he => hij (Prod.ext h he)
    exact Set.disjoint_left.1 (gridCell_disjoint h') hpi.2 hpj.2
  · exact Set.disjoint_left.1 (gridCell_disjoint h) hpi.1 hpj.1

lemma uniform_row_sum (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ j : Fin n, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) = (n : ℝ)⁻¹ := by
  have hd : Pairwise (fun j k : Fin n =>
      Disjoint (gridCell i ×ˢ gridCell j) (gridCell i ×ˢ gridCell k)) := by
    intro j k hjk
    exact Set.disjoint_left.2 (fun _ hp hq =>
      Set.disjoint_left.1 (gridCell_disjoint hjk) hp.2 hq.2)
  rw [← measureReal_iUnion_fintype hd (fun j => (gridCell_measurable i).prod (gridCell_measurable j))]
  have he : (⋃ j : Fin n, gridCell i ×ˢ gridCell j) = gridCell i ×ˢ Ioi (0 : I) := by
    rw [← prod_iUnion, gridCell_cover hn]
  rw [he]
  have hae : gridCell i ×ˢ Ioi (0 : I) =ᵐ[(μ : Measure (I × I))] Prod.fst ⁻¹' gridCell i := by
    filter_upwards [uniform_ae_pos μ hμ] with p hp
    change (p.1 ∈ gridCell i ∧ 0 < p.2) = (p.1 ∈ gridCell i)
    simp only [hp.2, and_true]
  rw [measureReal_congr hae]
  have hm := congrArg (fun ξ : Measure I => ξ.real (gridCell i)) hμ.1
  rw [map_measureReal_apply measurable_fst (gridCell_measurable i)] at hm
  rw [hm, measureReal_def, gridCell_volume]
  simp

lemma uniform_column_sum (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ j : Fin n, (μ : Measure (I × I)).real (gridCell j ×ˢ gridCell i) = (n : ℝ)⁻¹ := by
  have hd : Pairwise (fun j k : Fin n =>
      Disjoint (gridCell j ×ˢ gridCell i) (gridCell k ×ˢ gridCell i)) := by
    intro j k hjk
    exact Set.disjoint_left.2 (fun _ hp hq =>
      Set.disjoint_left.1 (gridCell_disjoint hjk) hp.1 hq.1)
  rw [← measureReal_iUnion_fintype hd (fun j => (gridCell_measurable j).prod (gridCell_measurable i))]
  have he : (⋃ j : Fin n, gridCell j ×ˢ gridCell i) = Ioi (0 : I) ×ˢ gridCell i := by
    rw [← iUnion_prod_const, gridCell_cover hn]
  rw [he]
  have hae : Ioi (0 : I) ×ˢ gridCell i =ᵐ[(μ : Measure (I × I))] Prod.snd ⁻¹' gridCell i := by
    filter_upwards [uniform_ae_pos μ hμ] with p hp
    change (0 < p.1 ∧ p.2 ∈ gridCell i) = (p.2 ∈ gridCell i)
    simp only [hp.1, true_and]
  rw [measureReal_congr hae]
  have hm := congrArg (fun ξ : Measure I => ξ.real (gridCell i)) hμ.2
  rw [map_measureReal_apply measurable_snd (gridCell_measurable i)] at hm
  rw [hm, measureReal_def, gridCell_volume]
  simp

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open Finset

lemma rounded_weights {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α)
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (q : ℕ) (hq : 0 < q) :
    ∃ c : α → ℕ, (∑ a, c a = q) ∧
      ∑ a, |(c a : ℝ) / q - w a| ≤ 2 * Fintype.card α / q := by
  let b : α → ℕ := fun a => ⌊(q : ℝ) * w a⌋₊
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hb a : (b a : ℝ) ≤ (q : ℝ) * w a := Nat.floor_le (mul_nonneg hq'.le (hw a))
  have hbs : (∑ a, b a : ℕ) ≤ q := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hb a)
    rw [← Finset.mul_sum, hs, mul_one] at h
    exact_mod_cast h
  let r := q - ∑ a, b a
  have hr : (r : ℝ) = (q : ℝ) - ∑ a, (b a : ℝ) := by
    simp only [r, Nat.cast_sub hbs, Nat.cast_sum]
  let c : α → ℕ := fun a => b a + if a = a₀ then r else 0
  refine ⟨c, ?_, ?_⟩
  · simp only [c, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Nat.add_sub_of_le hbs
  · have he a : 0 ≤ w a - (b a : ℝ) / q := by
      exact sub_nonneg.mpr ((div_le_iff₀ hq').2 (by simpa [mul_comm] using hb a))
    have he' a : w a - (b a : ℝ) / q ≤ (q : ℝ)⁻¹ := by
      have hf := Nat.lt_floor_add_one ((q : ℝ) * w a)
      have hb' : (q : ℝ) * w a < (b a : ℝ) + 1 := hf
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hq').2
      have hd : (w a - (b a : ℝ) / q) * q = (q : ℝ) * w a - b a := by field_simp
      rw [hd]
      linarith
    have hs' : ∑ a, (w a - (b a : ℝ) / q) = (r : ℝ) / q := by
      rw [Finset.sum_sub_distrib, hs, ← Finset.sum_div, hr]
      field_simp
    have hsum : (r : ℝ) / q ≤ (Fintype.card α : ℝ) / q := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => he' a)
      rw [hs'] at h
      simpa [div_eq_mul_inv] using h
    calc
      ∑ a, |(c a : ℝ) / q - w a| ≤
          ∑ a, ((w a - (b a : ℝ) / q) + if a = a₀ then (r : ℝ) / q else 0) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a = a₀
        · subst a
          have hr0 : (0 : ℝ) ≤ (r : ℝ) / q := by positivity
          dsimp [c]
          simp only [if_true, Nat.cast_add, add_div]
          rw [show (b a₀ : ℝ) / q + (r : ℝ) / q - w a₀ =
            - (w a₀ - (b a₀ : ℝ) / q) + (r : ℝ) / q by ring]
          exact (abs_add_le _ _).trans (by rw [abs_neg, abs_of_nonneg (he a₀), abs_of_nonneg hr0])
        · simp only [c, ha, if_false, add_zero]
          rw [abs_of_nonpos (sub_nonpos.mpr ((sub_nonneg.mp (he a))))]
          linarith
      _ = 2 * ((r : ℝ) / q) := by
        rw [Finset.sum_add_distrib, hs']
        simp
        ring
      _ ≤ 2 * (Fintype.card α : ℝ) / q  := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof

lemma exists_finite_copies {α : Type*} [Fintype α] (c : α → ℕ) {q : ℕ}
    (hc : ∑ a, c a = q) :
    ∃ label : Fin q → α, ∀ f : α → ℝ, ∑ r, f (label r) = ∑ a, (c a : ℝ) * f a := by
  classical
  have hcard : Fintype.card (Σ a, Fin (c a)) = Fintype.card (Fin q) := by
    simp [Fintype.card_sigma, hc]
  let e : (Σ a, Fin (c a)) ≃ Fin q := Fintype.equivOfCardEq hcard
  refine ⟨fun r => (e.symm r).1, ?_⟩
  intro f
  calc
    ∑ r, f (e.symm r).1 = ∑ a : (Σ a, Fin (c a)), f a.1 :=
      Equiv.sum_comp e.symm (fun a => f a.1)
    _ = ∑ a, (c a : ℝ) * f a := by simp [Fintype.sum_sigma]

lemma exists_rational_copies {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (q : ℕ) (hq : 0 < q) :
    ∃ (c : α → ℕ) (label : Fin q → α),
      (∑ a, c a = q) ∧
      (∀ f : α → ℝ, ∑ r, f (label r) = ∑ a, (c a : ℝ) * f a) ∧
      ∑ a, |(c a : ℝ) / q - w a| ≤ 2 * Fintype.card α / q := by
  classical
  obtain ⟨c, hc, he⟩ := rounded_weights (Classical.choice inferInstance) w hw hs q hq
  obtain ⟨label, hl⟩ := exists_finite_copies c hc
  exact ⟨c, label, hc, hl, he⟩

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open unitInterval Set

def fiberPermutation {m q : ℕ} (family : Fin q → Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m × Fin q) where
  toFun p := (family p.2 p.1, p.2)
  invFun p := ((family p.2).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

def blowupPermutation {m q : ℕ} (family : Fin q → Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m * q)) :=
  finProdFinEquiv.symm.trans ((fiberPermutation family).trans finProdFinEquiv)

lemma blowup_apply {m q : ℕ} (family : Fin q → Equiv.Perm (Fin m)) (i : Fin m) (r : Fin q) :
    blowupPermutation family (finProdFinEquiv (i, r)) = finProdFinEquiv (family r i, r) := by
  simp [blowupPermutation, fiberPermutation]

lemma blowup_grid_mem {m q : ℕ} (i : Fin m) (r : Fin q) :
    gridPoint (finProdFinEquiv (i, r)) ∈ gridCell i := by
  rw [mem_gridCell]
  change (i.val : ℝ) / m < ((r.val + q * i.val : ℕ) + 1 : ℝ) / (m * q : ℕ) ∧
    ((r.val + q * i.val : ℕ) + 1 : ℝ) / (m * q : ℕ) ≤ ((i.val : ℝ) + 1) / m
  have hm : (0 : ℝ) < m := by exact_mod_cast i.pos
  have hq : (0 : ℝ) < q := by exact_mod_cast r.pos
  have hr : (r.val : ℝ) + 1 ≤ q := by exact_mod_cast r.isLt
  have hr0 : (0 : ℝ) ≤ r.val := by positivity
  push_cast
  constructor
  · apply (div_lt_div_iff₀ hm (mul_pos hm hq)).2
    nlinarith
  · apply (div_le_div_iff₀ (mul_pos hm hq) hm).2
    nlinarith

lemma blowup_cell_pair {m q : ℕ} (family : Fin q → Equiv.Perm (Fin m)) (i : Fin m) (r : Fin q) :
    (gridPoint (finProdFinEquiv (i, r)),
      gridPoint (blowupPermutation family (finProdFinEquiv (i, r)))) ∈
      gridCell i ×ˢ gridCell (family r i) := by
  rw [blowup_apply]
  exact ⟨blowup_grid_mem i r, blowup_grid_mem (family r i) r⟩

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

lemma empiricalLaw_eq {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    (empiricalLaw π : Measure (I × I)) =
      (by letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
          exact (PMF.uniformOfFintype (Fin n)).toMeasure.map
            (fun i => (gridPoint i, gridPoint (π i)))) := by
  simp only [empiricalLaw, hn, ↓reduceDIte]
  rfl

lemma empirical_integral {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (f : I × I → ℝ) (hf : Measurable f) :
    ∫ z, f z ∂(empiricalLaw π : Measure (I × I)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i, gridPoint (π i)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [empiricalLaw_eq hn, integral_map (measurable_of_finite _).aemeasurable
    hf.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, Finset.mul_sum]

lemma empirical_first_integral {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (f : I → ℝ) (hf : Measurable f) :
    ∫ z, f z.1 ∂(empiricalLaw π : Measure (I × I)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i) :=
  empirical_integral hn π _ (hf.comp measurable_fst)

lemma empirical_second_integral {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (f : I → ℝ) (hf : Measurable f) :
    ∫ z, f z.2 ∂(empiricalLaw π : Measure (I × I)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i) := by
  have h := empirical_integral hn π (fun z => f z.2) (hf.comp measurable_snd)
  rw [h]
  congr 1
  exact Equiv.sum_comp π (fun i => f (gridPoint i))

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory Set Filter

lemma finite_partition_integral_bound {α J : Type*} [MeasurableSpace α] [Fintype J]
    [DecidableEq J] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : J → Set α) (hS : ∀ j, MeasurableSet (S j))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hc : ∀ᵐ x ∂μ, ∃ j, x ∈ S j) (v : J → ℝ) (f : α → ℝ)
    (hf : Integrable f μ) (δ : ℝ)
    (ho : ∀ j x, x ∈ S j → |f x - v j| ≤ δ) :
    |(∫ x, f x ∂μ) - ∑ j, μ.real (S j) * v j| ≤ δ := by
  let g : α → ℝ := fun x => ∑ j, (S j).indicator (fun _ => v j) x
  have hg : Integrable g μ := by
    apply integrable_finsetSum
    intro j _
    exact (integrable_const _).indicator (hS j)
  have hgj {j : J} {x : α} (hx : x ∈ S j) : g x = v j := by
    dsimp [g]
    rw [Finset.sum_eq_single j]
    · exact Set.indicator_of_mem hx _
    · intro k _ hkj
      apply Set.indicator_of_notMem
      exact fun hxk => Set.disjoint_left.1 (hd hkj) hxk hx
    · simp
  have hgi : ∫ x, g x ∂μ = ∑ j, μ.real (S j) * v j := by
    rw [integral_finsetSum _ (fun j _ => (integrable_const _).indicator (hS j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_indicator (hS j)]
    simp
  have hb : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ δ := by
    filter_upwards [hc] with x hx
    obtain ⟨j, hj⟩ := hx
    rw [hgj hj, Real.norm_eq_abs]
    exact ho j x hj
  have h := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hf hg, hgi, Real.norm_eq_abs] at h
  simpa using h

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set Matrix

def gridMatrix (μ : ProbabilityMeasure (I × I)) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => n * (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j)

lemma gridMatrix_stochastic (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) : gridMatrix μ n ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i j => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg, ?_, ?_⟩
  · intro i
    simp only [gridMatrix, ← Finset.mul_sum, uniform_row_sum μ hμ hn i, mul_inv_cancel₀ hn']
  · intro j
    simp only [gridMatrix, ← Finset.mul_sum, uniform_column_sum μ hμ hn j, mul_inv_cancel₀ hn']

lemma grid_birkhoff (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
      ∀ i j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) =
        (n : ℝ)⁻¹ * ∑ a, w a * (if a i = j then 1 else 0) := by
  obtain ⟨w, hw, hs, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (gridMatrix_stochastic μ hμ hn)
  refine ⟨w, hw, hs, ?_⟩
  intro i j
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, gridMatrix] at h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [h, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]

lemma birkhoff_quadrature {n : ℕ} (μ : ProbabilityMeasure (I × I))
    (w : Equiv.Perm (Fin n) → ℝ)
    (he : ∀ i j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) =
      (n : ℝ)⁻¹ * ∑ a, w a * (if a i = j then 1 else 0))
    (v : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) * v i j =
      ∑ a, w a * ((n : ℝ)⁻¹ * ∑ i, v i (a i)) := by
  simp_rw [he]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp [mul_assoc, mul_left_comm]

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open scoped BoundedContinuousFunction
open MeasureTheory unitInterval Set Filter Topology

def gridAverage {n : ℕ} (a : Equiv.Perm (Fin n)) (f : I × I → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i, gridPoint (a i))

lemma gridPoint_mem {n : ℕ} (i : Fin n) : gridPoint i ∈ gridCell i := by
  rw [mem_gridCell]
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  exact ⟨(div_lt_div_iff_of_pos_right hn).2 (by linarith), le_rfl⟩

lemma grid_pair_dist {n : ℕ} (i j : Fin n) {p : I × I}
    (hp : p ∈ gridCell i ×ˢ gridCell j) :
    dist p (gridPoint i, gridPoint j) ≤ (n : ℝ)⁻¹ := by
  rw [Prod.dist_eq]
  exact max_le (gridCell_diameter i hp.1 (gridPoint_mem i))
    (gridCell_diameter j hp.2 (gridPoint_mem j))

lemma gridAverage_bound {n : ℕ} (hn : 0 < n) (a : Equiv.Perm (Fin n))
    (f : I × I →ᵇ ℝ) : |gridAverage a f| ≤ ‖f‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gridAverage
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn')]
  have hs : |∑ i : Fin n, f (gridPoint i, gridPoint (a i))| ≤ (n : ℝ) * ‖f‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ i : Fin n, |f (gridPoint i, gridPoint (a i))| ≤ ∑ _i : Fin n, ‖f‖ :=
        Finset.sum_le_sum (fun i _ => f.norm_coe_le_norm _)
      _ = _ := by simp
  calc
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn'.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]

lemma grid_integral_bound (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (f : I × I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p q : I × I, dist p q ≤ (n : ℝ)⁻¹ → |f p - f q| ≤ δ) :
    |(∫ p, f p ∂(μ : Measure (I × I))) -
      ∑ i : Fin n, ∑ j : Fin n,
        (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) * f (gridPoint i, gridPoint j)| ≤ δ := by
  have h := finite_partition_integral_bound (μ : Measure (I × I))
    (fun j : Fin n × Fin n => gridCell j.1 ×ˢ gridCell j.2)
    (fun j => (gridCell_measurable j.1).prod (gridCell_measurable j.2))
    grid_square_disjoint (grid_square_cover μ hμ hn)
    (fun j => f (gridPoint j.1, gridPoint j.2)) f (f.integrable _) δ
    (fun j p hp => ho p _ (grid_pair_dist j.1 j.2 hp))
  simpa only [Fintype.sum_prod_type] using h

lemma grid_birkhoff_integral_bound (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (w : Equiv.Perm (Fin n) → ℝ)
    (he : ∀ i j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) =
      (n : ℝ)⁻¹ * ∑ a, w a * (if a i = j then 1 else 0))
    (f : I × I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p q : I × I, dist p q ≤ (n : ℝ)⁻¹ → |f p - f q| ≤ δ) :
    |(∫ p, f p ∂(μ : Measure (I × I))) - ∑ a, w a * gridAverage a f| ≤ δ := by
  have h := grid_integral_bound μ hμ hn f δ ho
  rw [birkhoff_quadrature μ w he] at h
  exact h

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open scoped BoundedContinuousFunction
open MeasureTheory unitInterval

lemma finite_average_error {α : Type*} [Fintype α] (hn : 0 < Fintype.card α)
    (f g : α → ℝ) (δ : ℝ) (h : ∀ a, |f a - g a| ≤ δ) :
    |(Fintype.card α : ℝ)⁻¹ * ∑ a, f a - (Fintype.card α : ℝ)⁻¹ * ∑ a, g a| ≤ δ := by
  have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr hn')]
  have hs : |∑ a, (f a - g a)| ≤ (Fintype.card α : ℝ) * δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => h a)
  calc
    _ ≤ (Fintype.card α : ℝ)⁻¹ * ((Fintype.card α : ℝ) * δ) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn'.le)
    _ = δ := by rw [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]

lemma double_average {m q : ℕ} (v : Fin m → Fin q → ℝ) :
    ((m * q : ℕ) : ℝ)⁻¹ * ∑ p : Fin m × Fin q, v p.1 p.2 =
      (q : ℝ)⁻¹ * ∑ r : Fin q, ((m : ℝ)⁻¹ * ∑ i : Fin m, v i r) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Nat.cast_mul, mul_inv_rev, ← Finset.mul_sum]
  ring

lemma blowup_integral_bound {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (family : Fin q → Equiv.Perm (Fin m)) (f : I × I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p r : I × I, dist p r ≤ (m : ℝ)⁻¹ → |f p - f r| ≤ δ) :
    |(∫ p, f p ∂(empiricalLaw (blowupPermutation family) : Measure (I × I))) -
      (q : ℝ)⁻¹ * ∑ r : Fin q, gridAverage (family r) f| ≤ δ := by
  rw [empirical_integral (Nat.mul_pos hm hq) _ f f.measurable]
  have he : (∑ k : Fin (m*q), f (gridPoint k, gridPoint (blowupPermutation family k))) =
      ∑ p : Fin m × Fin q, f (gridPoint (finProdFinEquiv p),
        gridPoint (finProdFinEquiv (family p.2 p.1,p.2))) := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    apply Finset.sum_congr rfl
    intro p _
    rcases p with ⟨i, r⟩
    rw [blowup_apply]
  rw [he]
  have h := finite_average_error (α := Fin m × Fin q)
    (by simpa using Nat.mul_pos hm hq)
    (fun p => f (gridPoint (finProdFinEquiv p), gridPoint (finProdFinEquiv (family p.2 p.1,p.2))))
    (fun p => f (gridPoint p.1, gridPoint (family p.2 p.1))) δ ?_
  · simp only [Fintype.card_prod, Fintype.card_fin] at h
    rw [double_average (fun i r => f (gridPoint i, gridPoint (family r i)))] at h
    exact h
  · intro p
    exact ho _ _ (grid_pair_dist p.1 (family p.2 p.1)
      ⟨blowup_grid_mem p.1 p.2, blowup_grid_mem (family p.2 p.1) p.2⟩)

lemma weighted_sum_error {α : Type*} [Fintype α] (u w v : α → ℝ) (M : ℝ)
    (hv : ∀ a, |v a| ≤ M) :
    |(∑ a, u a * v a) - ∑ a, w a * v a| ≤ M * ∑ a, |u a - w a| := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    ∑ a, |(u a - w a) * v a| ≤ ∑ a, |u a - w a| * M := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open scoped BoundedContinuousFunction
open MeasureTheory unitInterval

lemma finite_realization (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    (m : ℕ) (hm : 0 < m) :
    ∃ (n : ℕ) (π : Equiv.Perm (Fin n)), m ≤ n ∧ 0 < n ∧
      ∀ (f : I × I →ᵇ ℝ) (δ : ℝ),
        (∀ p r : I × I, dist p r ≤ (m : ℝ)⁻¹ → |f p - f r| ≤ δ) →
        |(∫ p, f p ∂(empiricalLaw π : Measure (I × I))) -
          ∫ p, f p ∂(μ : Measure (I × I))| ≤ 2 * δ + ‖f‖ / m := by
  classical
  obtain ⟨w, hw, hs, he⟩ := grid_birkhoff μ hμ hm
  let q := m * (2 * Fintype.card (Equiv.Perm (Fin m)))
  have hc : 0 < Fintype.card (Equiv.Perm (Fin m)) := Fintype.card_pos
  have hq : 0 < q := Nat.mul_pos hm (Nat.mul_pos (by omega) hc)
  obtain ⟨c, label, _hc, hl, herr⟩ := exists_rational_copies w hw hs q hq
  refine ⟨m*q, blowupPermutation label, ?_, Nat.mul_pos hm hq, ?_⟩
  · exact Nat.le_mul_of_pos_right m hq
  intro f δ ho
  have hfirst := blowup_integral_bound hm hq label f δ ho
  have hlast := grid_birkhoff_integral_bound μ hμ hm w he f δ ho
  have havg : (q : ℝ)⁻¹ * ∑ r, gridAverage (label r) f =
      ∑ a, ((c a : ℝ) / q) * gridAverage a f := by
    rw [hl (fun a => gridAverage a f), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [havg] at hfirst
  have hmiddle := weighted_sum_error (fun a => (c a : ℝ) / q) w
    (fun a => gridAverage a f) ‖f‖ (fun a => gridAverage_bound hm a f)
  have hratio : (2 : ℝ) * Fintype.card (Equiv.Perm (Fin m)) / q = (m : ℝ)⁻¹ := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hc' : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    dsimp [q]
    push_cast
    field_simp
  have hmid : |(∑ a, ((c a : ℝ) / q) * gridAverage a f) -
      ∑ a, w a * gridAverage a f| ≤ ‖f‖ / m := by
    apply hmiddle.trans
    calc
      _ ≤ ‖f‖ * (2 * Fintype.card (Equiv.Perm (Fin m)) / q) :=
        mul_le_mul_of_nonneg_left herr (norm_nonneg _)
      _ = _ := by rw [hratio, div_eq_mul_inv]
  have htri := abs_sub_le (∫ p, f p ∂(empiricalLaw (blowupPermutation label) : Measure (I × I)))
    (∑ a, ((c a : ℝ) / q) * gridAverage a f) (∫ p, f p ∂(μ : Measure (I × I)))
  have htri' := abs_sub_le (∑ a, ((c a : ℝ) / q) * gridAverage a f)
    (∑ a, w a * gridAverage a f) (∫ p, f p ∂(μ : Measure (I × I)))
  rw [abs_sub_comm (∫ p, f p ∂(μ : Measure (I × I)))] at hlast
  linarith

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open scoped BoundedContinuousFunction
open MeasureTheory unitInterval Filter Topology

lemma inverse_size_tendsto {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun j => (m j : ℝ)⁻¹) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hm

lemma weak_of_grid_error (μ : ProbabilityMeasure (I × I))
    (ν : ℕ → ProbabilityMeasure (I × I)) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (he : ∀ j (f : I × I →ᵇ ℝ) (δ : ℝ),
      (∀ p r : I × I, dist p r ≤ (m j : ℝ)⁻¹ → |f p - f r| ≤ δ) →
      |(∫ p, f p ∂(ν j : Measure (I × I))) - ∫ p, f p ∂(μ : Measure (I × I))| ≤
        2 * δ + ‖f‖ / m j) : Tendsto ν atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, hos⟩ := Metric.uniformContinuous_iff_le.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 4) (by positivity)
  have hi := inverse_size_tendsto hm
  have hi' : Tendsto (fun j => ‖f‖ / (m j : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul ‖f‖
  have hd' : ∀ᶠ j in atTop, (m j : ℝ)⁻¹ < d := hi.eventually (gt_mem_nhds hd)
  have he' : ∀ᶠ j in atTop, ‖f‖ / (m j : ℝ) < ε / 2 :=
    hi'.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hd'.and he')
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨hdj, hej⟩ := hN j hj
  have hb := he j f (ε / 4) (fun p r hpr => by
    simpa only [Real.dist_eq] using hos (hpr.trans hdj.le))
  rw [Real.dist_eq]
  linarith

lemma empirical_realization (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ) :
    ∃ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n),
      (∀ j, 0 < (s j).1) ∧ Tendsto (fun j => (s j).1) atTop atTop ∧
      Tendsto (fun j => empiricalLaw (s j).2) atTop (𝓝 μ) := by
  classical
  have h := fun j => finite_realization μ hμ (j+1) (Nat.succ_pos j)
  choose n π hn hp he using h
  refine ⟨fun j => ⟨n j, π j⟩, hp, ?_, ?_⟩
  · apply tendsto_atTop_mono hn
    exact tendsto_add_atTop_nat 1
  · apply weak_of_grid_error μ (fun j => empiricalLaw (π j)) (fun j => j+1)
      (tendsto_add_atTop_nat 1)
    exact he

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set Filter Topology
open scoped BoundedContinuousFunction ENNReal

lemma grid_line_integral_bound {n : ℕ} (hn : 0 < n) (f : I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p r : I, dist p r ≤ (n : ℝ)⁻¹ → |f p - f r| ≤ δ) :
    |(∫ p : I, f p) - (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i)| ≤ δ := by
  have hc : ∀ᵐ x : I, ∃ i : Fin n, x ∈ gridCell i := by
    filter_upwards [volume_ae_pos] with x hx
    exact mem_iUnion.1 ((gridCell_cover hn).symm ▸ hx)
  have h := finite_partition_integral_bound (volume : Measure I) gridCell gridCell_measurable
    gridCell_disjoint hc (fun i => f (gridPoint i)) f (f.integrable _) δ
    (fun i x hx => ho x _ (gridCell_diameter i hx (gridPoint_mem i)))
  simpa only [measureReal_def, gridCell_volume, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.mul_sum] using h

lemma grid_line_integral_tendsto {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    (f : I →ᵇ ℝ) :
    Tendsto (fun j => (m j : ℝ)⁻¹ * ∑ i : Fin (m j), f (gridPoint i))
      atTop (𝓝 (∫ p : I, f p)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, ho⟩ := Metric.uniformContinuous_iff_le.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) (by positivity)
  have hi : Tendsto (fun j => (m j : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hm
  have hd' := hi.eventually (gt_mem_nhds hd)
  have hp : ∀ᶠ j in atTop, 0 < m j := hm.eventually (eventually_gt_atTop 0)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hd'.and hp)
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨hdj, hpj⟩ := hN j hj
  have h := grid_line_integral_bound hpj f (ε / 2) (fun p r hpr => by
    simpa only [Real.dist_eq] using ho (hpr.trans hdj.le))
  rw [Real.dist_eq, abs_sub_comm]
  exact h.trans_lt (by linarith)

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Filter Topology
open scoped BoundedContinuousFunction

def uniformLaw : ProbabilityMeasure I := ⟨volume, inferInstance⟩

lemma empirical_marginal_tendsto (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop)
    (g : I × I → I) (hg : Continuous g)
    (he : ∀ j, 0 < (s j).1 → ∀ f : I →ᵇ ℝ,
      (∫ p, f (g p) ∂(empiricalLaw (s j).2 : Measure (I × I))) =
        ((s j).1 : ℝ)⁻¹ * ∑ i : Fin (s j).1, f (gridPoint i)) :
    Tendsto (fun j => (empiricalLaw (s j).2).map hg.measurable.aemeasurable)
      atTop (𝓝 uniformLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have h := grid_line_integral_tendsto hs f
  apply h.congr'
  filter_upwards [hs.eventually (eventually_gt_atTop 0)] with j hj
  change _ = ∫ p, f p ∂((empiricalLaw (s j).2 : Measure (I × I)).map g)
  have hf : AEStronglyMeasurable (fun p : I => f p)
      ((empiricalLaw (s j).2 : Measure (I × I)).map g) := f.continuous.aestronglyMeasurable
  rw [integral_map hg.measurable.aemeasurable hf, he j hj f]

lemma empirical_limit_uniform (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop)
    {μ : ProbabilityMeasure (I × I)}
    (h : Tendsto (fun j => empiricalLaw (s j).2) atTop (𝓝 μ)) : UniformMarginals μ := by
  have hx := empirical_marginal_tendsto s hs Prod.fst continuous_fst
    (fun j hj f => empirical_first_integral hj (s j).2 f f.measurable)
  have hy := empirical_marginal_tendsto s hs Prod.snd continuous_snd
    (fun j hj f => empirical_second_integral hj (s j).2 f f.measurable)
  have hx' := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h continuous_fst
  have hy' := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h continuous_snd
  have ex := tendsto_nhds_unique hx' hx
  have ey := tendsto_nhds_unique hy' hy
  exact ⟨congrArg (fun ν : ProbabilityMeasure I => (ν : Measure I)) ex,
    congrArg (fun ν : ProbabilityMeasure I => (ν : Measure I)) ey⟩

end PermutationLimitProof


namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set

lemma frontier_finite_union {α ι : Type*} [TopologicalSpace α] (s : Finset ι)
    (A : ι → Set α) : frontier (⋃ i ∈ s, A i) ⊆ ⋃ i ∈ s, frontier (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    intro x hx
    rcases frontier_union_subset (A i) (⋃ j ∈ s, A j) hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr (ih hx.2)

lemma frontier_finite_iUnion {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    (A : ι → Set α) : frontier (⋃ i, A i) ⊆ ⋃ i, frontier (A i) := by
  simpa using frontier_finite_union (Finset.univ : Finset ι) A

lemma frontier_finite_iInter {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    (A : ι → Set α) : frontier (⋂ i, A i) ⊆ ⋃ i, frontier (A i) := by
  simpa only [← compl_iInter, frontier_compl] using
    frontier_finite_iUnion (fun i => (A i)ᶜ)

lemma patternEvent_chain {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    patternEvent τ = {p | ∃ ρ : Equiv.Perm (Fin k),
      StrictMono (fun i => (p (ρ i)).1) ∧
      StrictMono (fun i => (p (ρ (τ.symm i))).2)} := by
  ext p
  constructor
  · rintro ⟨ρ, hx, hy⟩
    refine ⟨ρ, hx, ?_⟩
    intro i j hij
    exact (hy (τ.symm i) (τ.symm j)).mpr (by simpa using hij)
  · rintro ⟨ρ, hx, hy⟩
    refine ⟨ρ, hx, ?_⟩
    intro i j
    simpa using (hy.lt_iff_lt (a := τ i) (b := τ j))

abbrev OrderedPair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def horizontalChain {k : ℕ} (ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  ⋂ q : OrderedPair k, {p | (p (ρ q.val.1)).1 < (p (ρ q.val.2)).1}

def verticalChain {k : ℕ} (ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  ⋂ q : OrderedPair k, {p | (p (ρ q.val.1)).2 < (p (ρ q.val.2)).2}

lemma patternEvent_union {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    patternEvent τ = ⋃ ρ : Equiv.Perm (Fin k),
      horizontalChain ρ ∩ verticalChain (τ.symm.trans ρ) := by
  rw [patternEvent_chain]
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, horizontalChain, verticalChain, mem_inter_iff,
    mem_iInter, Equiv.trans_apply]
  constructor
  · rintro ⟨ρ, hx, hy⟩
    exact ⟨ρ, fun q => hx q.property, fun q => hy q.property⟩
  · rintro ⟨ρ, hx, hy⟩
    exact ⟨ρ, fun i j hij => hx ⟨(i,j),hij⟩, fun i j hij => hy ⟨(i,j),hij⟩⟩

lemma patternEvent_isOpen {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    IsOpen (patternEvent τ) := by
  rw [patternEvent_union]
  apply isOpen_iUnion
  intro ρ
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite fun q =>
      isOpen_lt (continuous_apply _ |>.fst) (continuous_apply _ |>.fst)
  · exact isOpen_iInter_of_finite fun q =>
      isOpen_lt (continuous_apply _ |>.snd) (continuous_apply _ |>.snd)

lemma patternEvent_frontier_subset {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    frontier (patternEvent τ) ⊆ {p | ∃ i j : Fin k, i ≠ j ∧
      ((p i).1 = (p j).1 ∨ (p i).2 = (p j).2)} := by
  rw [patternEvent_union]
  intro p hp
  obtain ⟨ρ, hρ⟩ := mem_iUnion.mp (frontier_finite_iUnion _ hp)
  rcases frontier_inter_subset _ _ hρ with hx | hy
  · obtain ⟨q, hq⟩ := mem_iUnion.mp (frontier_finite_iInter _ hx.1)
    exact ⟨ρ q.val.1, ρ q.val.2, fun h => (ne_of_lt q.property) (ρ.injective h),
      Or.inl (frontier_lt_subset_eq (continuous_apply _ |>.fst)
        (continuous_apply _ |>.fst) hq)⟩
  · obtain ⟨q, hq⟩ := mem_iUnion.mp (frontier_finite_iInter _ hy.2)
    exact ⟨ρ (τ.symm q.val.1), ρ (τ.symm q.val.2),
      fun h => (ne_of_lt q.property) (τ.symm.injective (ρ.injective h)),
      Or.inr (frontier_lt_subset_eq (continuous_apply _ |>.snd)
        (continuous_apply _ |>.snd) hq)⟩

end PermutationLimitProof


namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval PermLimits.Shared Set Filter Topology

lemma unit_diagonal_null :
    (volume.prod volume : Measure (I × I)) {p | p.1 = p.2} = 0 := by
  apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
  exact Filter.Eventually.of_forall fun x => by
    have he : Prod.mk x ⁻¹' {p : I × I | p.1=p.2} = {x} := by ext y; simp [eq_comm]
    change volume (Prod.mk x ⁻¹' {p : I × I | p.1=p.2}) = 0
    rw [he]
    simp

lemma coordinate_collision_null {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (c : I × I → I) (hc : Measurable c) (hm : (μ : Measure (I × I)).map c = volume)
    {i j : Fin k} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I)))
      {p | c (p i) = c (p j)} = 0 := by
  let ν := Measure.pi fun _ : Fin k => (μ : Measure (I × I))
  have hf (a : Fin k) : Measurable (fun p : Fin k → I × I => c (p a)) :=
    hc.comp (measurable_pi_apply a)
  have hind := (iIndepFun_pi (μ := fun _ : Fin k => (μ : Measure (I × I)))
    (X := fun _ => c) (fun _ => hc.aemeasurable)).indepFun hij
  have hmap (a : Fin k) : ν.map (fun p => c (p a)) = volume := by
    rw [show (fun p : Fin k → I × I => c (p a)) = c ∘ Function.eval a from rfl,
      ← Measure.map_map hc (measurable_pi_apply a),
      (measurePreserving_eval (fun _ : Fin k => (μ : Measure (I × I))) a).map_eq, hm]
  have hpair := hind.map_prod_eq_prod_map_map (hf i).aemeasurable (hf j).aemeasurable
  change ν.map (fun p => (c (p i), c (p j))) = _ at hpair
  rw [hmap i, hmap j] at hpair
  have hv := congrArg (fun η : Measure (I × I) => η {p | p.1=p.2}) hpair
  rw [Measure.map_apply ((hf i).prodMk (hf j))
    (show MeasurableSet {p : I × I | p.1=p.2} from measurableSet_diagonal),
    unit_diagonal_null] at hv
  exact hv

lemma patternEvent_frontier_null {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (τ : Equiv.Perm (Fin k)) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))) (frontier (patternEvent τ)) = 0 := by
  let ν := Measure.pi fun _ : Fin k => (μ : Measure (I × I))
  have hz : ν {p | ∃ i j : Fin k, i ≠ j ∧
      ((p i).1 = (p j).1 ∨ (p i).2 = (p j).2)} = 0 := by
    have he : {p : Fin k → I × I | ∃ i j : Fin k, i ≠ j ∧
        ((p i).1 = (p j).1 ∨ (p i).2 = (p j).2)} =
        ⋃ i : Fin k, ⋃ j : Fin k, ⋃ (_ : i ≠ j),
          ({p | (p i).1 = (p j).1} ∪ {p | (p i).2 = (p j).2}) := by ext p; simp
    rw [he]
    apply measure_iUnion_null
    intro i
    apply measure_iUnion_null
    intro j
    apply measure_iUnion_null
    intro hij
    exact measure_union_null
      (coordinate_collision_null μ Prod.fst measurable_fst hμ.1 hij)
      (coordinate_collision_null μ Prod.snd measurable_snd hμ.2 hij)
  exact measure_mono_null (patternEvent_frontier_subset τ) hz

lemma patternProbability_tendsto {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure (I × I)}
    {μ : ProbabilityMeasure (I × I)} (h : Tendsto μs l (𝓝 μ)) (hμ : UniformMarginals μ)
    {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Tendsto (fun a => patternProbability (μs a) τ) l (𝓝 (patternProbability μ τ)) := by
  have hp : Tendsto (fun a => ProbabilityMeasure.pi (fun _ : Fin k => μs a)) l
      (𝓝 (ProbabilityMeasure.pi (fun _ : Fin k => μ))) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun _ => h)
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hp
    (patternEvent_frontier_null μ hμ τ)
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp he

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set

abbrev Occurrence {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :=
  {x : Fin k → Fin n // StrictMono x ∧ ∀ i j, (π (x i) < π (x j) ↔ τ i < τ j)}

abbrev PatternTuple {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :=
  {x : Fin k → Fin n // ∃ ρ : Equiv.Perm (Fin k),
    StrictMono (x ∘ ρ) ∧ ∀ i j, (π (x (ρ i)) < π (x (ρ j)) ↔ τ i < τ j)}

def occurrenceTuple {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (p : Occurrence τ π × Equiv.Perm (Fin k)) : PatternTuple τ π :=
  ⟨p.1.val ∘ p.2.symm, p.2, by simpa only [Function.comp_def, Equiv.symm_apply_apply] using p.1.property⟩

lemma occurrenceTuple_bijective {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    Function.Bijective (occurrenceTuple τ π) := by
  constructor
  · rintro ⟨x,ρ⟩ ⟨y,η⟩ h
    have he : x.val ∘ ρ.symm = y.val ∘ η.symm := congrArg Subtype.val h
    have hr : Set.range x.val = Set.range y.val := by
      have hh := congrArg Set.range he
      simpa only [ρ.symm.surjective.range_comp, η.symm.surjective.range_comp] using hh
    have hxy : x = y := Subtype.ext ((x.property.1.range_inj y.property.1).mp hr)
    subst y
    have hrs : ρ.symm = η.symm := by
      apply Equiv.ext
      intro i
      exact x.property.1.injective (congrFun he i)
    have hρη : ρ = η := by simpa using congrArg Equiv.symm hrs
    subst η
    rfl
  · rintro ⟨x,ρ,hx,hy⟩
    refine ⟨(⟨x ∘ ρ, hx, hy⟩,ρ), ?_⟩
    apply Subtype.ext
    funext i
    exact congrArg x (ρ.apply_symm_apply i)

lemma patternTuple_card {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    Fintype.card (PatternTuple τ π) = occurrences τ π * Nat.factorial k := by
  classical
  have h := Fintype.card_congr (Equiv.ofBijective (occurrenceTuple τ π)
    (occurrenceTuple_bijective τ π))
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] at h
  have ho : Fintype.card (Occurrence τ π) = occurrences τ π := by
    change Fintype.card {x : Fin k → Fin n // _} = _
    rw [Fintype.card_subtype]
    unfold occurrences
    congr 1
  rw [ho] at h
  exact h.symm

lemma gridPoint_strictMono {n : ℕ} : StrictMono (@gridPoint n) := by
  intro i j hij
  change ((i.val : ℝ)+1)/n < ((j.val : ℝ)+1)/n
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast i.pos)).mpr
    (by exact_mod_cast Nat.add_lt_add_right hij 1)

lemma empirical_pattern_iff {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (x : Fin k → Fin n) :
    (fun i => (gridPoint (x i), gridPoint (π (x i)))) ∈ patternEvent τ ↔
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ) ∧
      ∀ i j, (π (x (ρ i)) < π (x (ρ j)) ↔ τ i < τ j) := by
  simp only [patternEvent, mem_ofPred_eq, gridPoint_strictMono.lt_iff_lt, StrictMono,
    Function.comp_def]

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval PermLimits.Shared Set
open scoped ENNReal

lemma pi_uniform_fin (k n : ℕ) [NeZero n] :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin n)).toMeasure) =
      (PMF.uniformOfFintype (Fin k → Fin n)).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fin, Fintype.card_fun, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

lemma empirical_pattern_probability {k n : ℕ} (hn : 0<n)
    (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    patternProbability (empiricalLaw π) τ =
      (occurrences τ π : ℝ) * Nat.factorial k / (n : ℝ)^k := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let g : Fin n → I × I := fun i => (gridPoint i, gridPoint (π i))
  have hg : Measurable g := measurable_of_finite _
  have hm : Measure.pi (fun _ : Fin k => (empiricalLaw π : Measure (I × I))) =
      (PMF.uniformOfFintype (Fin k → Fin n)).toMeasure.map (fun x i => g (x i)) := by
    simp_rw [empiricalLaw_eq hn]
    rw [← Measure.pi_map_pi (fun _ : Fin k => hg.aemeasurable), pi_uniform_fin]
  have hc : Fintype.card {x : Fin k → Fin n | (fun i => g (x i)) ∈ patternEvent τ} =
      occurrences τ π * Nat.factorial k := by
    calc
      _ = Fintype.card (PatternTuple τ π) :=
        Fintype.card_congr (Equiv.subtypeEquivRight (empirical_pattern_iff τ π))
      _ = _ := patternTuple_card τ π
  have hs : MeasurableSet ((fun x : Fin k → Fin n => fun i => g (x i)) ⁻¹' patternEvent τ) :=
    (patternEvent_isOpen τ).measurableSet.preimage (measurable_of_finite _)
  rw [patternProbability, measureReal_def, hm,
    Measure.map_apply (measurable_of_finite _) (patternEvent_isOpen τ).measurableSet,
    PMF.toMeasure_uniformOfFintype_apply _ hs]
  change (↑(Fintype.card {x : Fin k → Fin n | (fun i => g (x i)) ∈ patternEvent τ}) /
    ↑(Fintype.card (Fin k → Fin n)) : ℝ≥0∞).toReal = _
  rw [hc]
  simp only [Fintype.card_fun, Fintype.card_fin, ENNReal.toReal_div,
    Nat.cast_mul, Nat.cast_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set Filter Topology

def collisionFactor (k n : ℕ) : ℝ := ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n)

lemma collisionFactor_formula {k n : ℕ} (hn : 0<n) (hk : k≤n) :
    collisionFactor k n = ((Nat.factorial k : ℝ) * Nat.choose n k) / (n : ℝ)^k := by
  have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  calc
    collisionFactor k n = ∏ i ∈ Finset.range k, ((n-i : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hin : i≤n := (Finset.mem_range.mp hi).le.trans hk
      rw [Nat.cast_sub hin]
      field_simp
    _ = (n.descFactorial k : ℝ) / (n : ℝ)^k := by
      rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range]
      simp
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

lemma collisionFactor_pos {k n : ℕ} (hn : 0<n) (hk : k≤n) : 0<collisionFactor k n := by
  rw [collisionFactor_formula hn hk]
  have hc : 0<Nat.choose n k := Nat.choose_pos hk
  have hf : 0<Nat.factorial k := Nat.factorial_pos k
  positivity

lemma empirical_pattern_factor {k n : ℕ} (hn : 0<n) (hk : k≤n)
    (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    patternProbability (empiricalLaw π) τ = collisionFactor k n * permDensity τ π := by
  rw [empirical_pattern_probability hn, collisionFactor_formula hn hk, permDensity, if_pos hk]
  have hc : (Nat.choose n k : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp

lemma collisionFactor_tendsto (k : ℕ) :
    Tendsto (collisionFactor k) atTop (𝓝 (1 : ℝ)) := by
  have h (i : ℕ) : Tendsto (fun n : ℕ => 1 - (i : ℝ)/n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))
  change Tendsto (fun n : ℕ => ∏ i ∈ Finset.range k, (1 - (i : ℝ)/n)) atTop (𝓝 (1 : ℝ))
  simpa only [Finset.prod_const_one] using
    tendsto_finsetProd (Finset.range k) (fun i _ => h i)

lemma empirical_pattern_tendsto_iff (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) {k : ℕ}
    (τ : Equiv.Perm (Fin k)) (a : ℝ) :
    Tendsto (fun m => permDensity τ (s m).2) atTop (𝓝 a) ↔
    Tendsto (fun m => patternProbability (empiricalLaw (s m).2) τ) atTop (𝓝 a) := by
  have hf := (collisionFactor_tendsto k).comp hs
  have hn : ∀ᶠ m in atTop, max 1 k ≤ (s m).1 := hs.eventually (eventually_ge_atTop _)
  have he : (fun m => patternProbability (empiricalLaw (s m).2) τ) =ᶠ[atTop]
      (fun m => collisionFactor k (s m).1 * permDensity τ (s m).2) := by
    filter_upwards [hn] with m hm
    exact empirical_pattern_factor (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm))
      ((le_max_right _ _).trans hm) τ (s m).2
  constructor
  · intro hd
    simpa only [one_mul] using (hf.mul hd).congr' he.symm
  · intro hp
    have he' : (fun m => permDensity τ (s m).2) =ᶠ[atTop]
        (fun m => patternProbability (empiricalLaw (s m).2) τ / collisionFactor k (s m).1) := by
      filter_upwards [hn, he] with m hm hem
      have hpos := collisionFactor_pos
        (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm))
        ((le_max_right _ _).trans hm)
      rw [hem]
      field_simp
    simpa only [div_one] using (hp.div hf one_ne_zero).congr' he'.symm

lemma empirical_weak_implies_densities (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop)
    {μ : ProbabilityMeasure (I × I)}
    (hweak : Tendsto (fun m => empiricalLaw (s m).2) atTop (𝓝 μ)) (hμ : UniformMarginals μ)
    {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Tendsto (fun m => permDensity τ (s m).2) atTop (𝓝 (patternProbability μ τ)) :=
  (empirical_pattern_tendsto_iff s hs τ _).mpr (patternProbability_tendsto hweak hμ τ)

end PermutationLimitProof


noncomputable section
namespace PermutationLimitProof
open MeasureTheory PermLimits.Shared unitInterval Filter Topology

lemma convergent_has_native_limit (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hc : IsConvergent s) (hs : Tendsto (fun m => (s m).1) atTop atTop) :
    ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ ConvergesTo s Z := by
  obtain ⟨μ, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq (fun j => empiricalLaw (s j).2)
  have hsize : Tendsto (fun j => (s (φ j)).1) atTop atTop := hs.comp hφ.tendsto_atTop
  have hμ := empirical_limit_uniform (fun j => s (φ j)) hsize hweak
  obtain ⟨Z, hZ, he⟩ := law_representation μ hμ
  refine ⟨Z, hZ, hs, ?_⟩
  intro k τ
  obtain ⟨a, ha⟩ := hc k τ
  have hsub := empirical_weak_implies_densities (fun j => s (φ j)) hsize hweak hμ τ
  have ha' := ha.comp hφ.tendsto_atTop
  have heq : a = patternProbability μ τ := tendsto_nhds_unique ha' hsub
  have hden : patternProbability μ τ = limitDensity τ Z := by
    unfold patternProbability limitDensity
    rw [he]
  rw [← hden, ← heq]
  exact ha

lemma native_limit_realized (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    ∃ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), (∀ m, 1 ≤ (s m).1) ∧ ConvergesTo s Z := by
  obtain ⟨s, hp, hs, hw⟩ := empirical_realization (nativeLaw Z hZ) (nativeLaw_uniform hZ)
  refine ⟨s, fun j => hp j, hs, ?_⟩
  intro k τ
  exact empirical_weak_implies_densities s hs hw (nativeLaw_uniform hZ) τ

theorem full_native_result :
    (∀ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), IsConvergent s →
        Tendsto (fun m => (s m).1) atTop atTop →
        ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ ConvergesTo s Z) ∧
    (∀ Z : I → I → ℝ, IsLimitPerm Z →
        ∃ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), (∀ m, 1 ≤ (s m).1) ∧ ConvergesTo s Z) :=
  ⟨convergent_has_native_limit, native_limit_realized⟩

end PermutationLimitProof


open PermLimits.Shared

namespace PermLimits.Existence

open Filter unitInterval

/-- **Theorem 1.6 (Main result)** (Hoppen et al., *Limits of permutation sequences*,
arXiv:1103.5844v2, p. 4).
(i) Given a convergent permutation sequence `(σ_m)` for which `|σ_m| → ∞`, there exists a limit
permutation `Z` such that `σ_m → Z`.
(ii) Conversely, every `Z ∈ 𝒵` is a limit of a convergent permutation sequence, i.e. there is a
sequence `(σ_m)` such that `σ_m → Z`.

**Formalization Note.** The two parts are one conjunction. Convergence of the sequence
(Definition 1.2, `IsConvergent`) is the hypothesis of (i), and `σ_m → Z` (Definition 1.5,
`ConvergesTo`, which includes `|σ_m| → ∞`) its conclusion. In (ii) the sequence consists of
genuine permutations, `|σ_m| ≥ 1` (the paper's `S_n` has `n ≥ 1`); `σ_m → Z` implies that the
sequence is convergent. Sequences are named `s` (`σ` is reserved notation once `unitInterval` is
opened). -/
theorem limit_permutation_exists_and_realized :
    (∀ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), IsConvergent s →
        Tendsto (fun m => (s m).1) atTop atTop →
        ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ ConvergesTo s Z) ∧
    (∀ Z : I → I → ℝ, IsLimitPerm Z →
        ∃ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), (∀ m, 1 ≤ (s m).1) ∧ ConvergesTo s Z) := by
  exact PermutationLimitProof.full_native_result 

end PermLimits.Existence

open PermLimits.Existence Filter unitInterval

theorem solution :
    (∀ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), IsConvergent s →
        Tendsto (fun m => (s m).1) atTop atTop →
        ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ ConvergesTo s Z) ∧
    (∀ Z : I → I → ℝ, IsLimitPerm Z →
        ∃ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), (∀ m, 1 ≤ (s m).1) ∧ ConvergesTo s Z) := PermLimits.Existence.limit_permutation_exists_and_realized 
