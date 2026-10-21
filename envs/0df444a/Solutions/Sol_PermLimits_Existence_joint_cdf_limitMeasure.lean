-- Prove2me | solution 1 for PermLimits.Existence.joint_cdf_limitMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T10:58:43.058445+00:00
-- url     : https://prove2.me/submissions/754fd885-741e-43f5-86c2-4aee4682db9a

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure

set_option autoImplicit false

open PermLimits.Shared

namespace P577

open MeasureTheory unitInterval Filter Topology Set

theorem quantile_le_iff (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (t u y : I) :
    quantile Z t u ≤ y ↔ (u : ℝ) ≤ Z t y := by
  obtain ⟨_, _, hcdf, _⟩ := hZ
  have hmono : Monotone (Z t) := (hcdf t).1
  have hone : Z t 1 = 1 := (hcdf t).2.2.2
  constructor
  · intro h
    set s := quantile Z t u with hs_def
    suffices hs : (u : ℝ) ≤ Z t s from hs.trans (hmono h)
    by_cases h1 : s = 1
    · rw [h1, hone]; exact u.2.2
    have hs1 : s < 1 := lt_of_le_of_ne le_top h1
    by_contra hlt
    push Not at hlt
    have hev : {z : I | Z t z < u} ∈ 𝓝[≥] s :=
      ((hcdf t).2.1 s).eventually (Iio_mem_nhds hlt)
    obtain ⟨c, hc, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' hs1).1 hev
    have hc' : sInf {y : I | (u : ℝ) ≤ Z t y} < c := hc
    obtain ⟨z, hz, hzc⟩ := sInf_lt_iff.1 hc'
    have hsz : s ≤ z := sInf_le hz
    have hlt2 : Z t z < u := hsub ⟨hsz, hzc⟩
    exact absurd hz (not_le.2 hlt2)
  · intro h
    exact sInf_le h

theorem aesm_section (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (y : I) :
    AEStronglyMeasurable (fun t => Z t y) volume := by
  obtain ⟨hmeas, _, hcdf, _⟩ := hZ
  have hsw : AEStronglyMeasurable (fun p : I × I => Z p.2 p.1)
      ((volume : Measure I).prod volume) := by
    have h1 : AEStronglyMeasurable (Function.uncurry Z) ((volume : Measure I).prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hmeas.aestronglyMeasurable
    exact h1.comp_measurePreserving Measure.measurePreserving_swap
  have hae : ∀ᵐ y ∂(volume : Measure I), AEStronglyMeasurable (fun t => Z t y) volume :=
    hsw.prodMk_left
  by_cases h1 : y = 1
  · subst h1
    have : (fun t => Z t 1) = fun _ => (1 : ℝ) := funext fun t => (hcdf t).2.2.2
    rw [this]; exact aestronglyMeasurable_const
  have hy : y < 1 := lt_of_le_of_ne le_top h1
  have hdense : Dense {y : I | AEStronglyMeasurable (fun t => Z t y) volume} := by
    apply dense_of_exists_between
    intro a b hab
    by_contra hcon
    push Not at hcon
    have hnull : volume (Ioo a b) = 0 := by
      apply measure_mono_null _ (ae_iff.1 hae)
      intro c hc hcG
      exact hcon c hcG hc
    have hsub : Iio b ⊆ Iic a ∪ Ioo a b := by
      intro c hc
      rcases le_or_gt c a with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hc⟩
    have hle := (measure_mono (μ := (volume : Measure I)) hsub).trans (measure_union_le _ _)
    rw [volume_Iio, volume_Iic, hnull, add_zero] at hle
    have hle2 := (ENNReal.ofReal_le_ofReal_iff a.2.1).1 hle
    exact absurd (Subtype.coe_lt_coe.2 hab) (not_lt.2 hle2)
  obtain ⟨u, -, hu, hlim⟩ := hdense.exists_seq_strictAnti_tendsto_of_lt hy
  have hlim' : Tendsto u atTop (𝓝[≥] y) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hu n).1.1.le⟩
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n t => Z t (u n))
    (fun n => (hu n).2) ?_
  exact Eventually.of_forall fun t => ((hcdf t).2.1 y).tendsto.comp hlim'

theorem aemeasurable_quantile (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    AEMeasurable (fun p : I × I => quantile Z p.1 p.2) volume := by
  apply NullMeasurable.aemeasurable
  have key : ∀ y : I,
      NullMeasurableSet ((fun p : I × I => quantile Z p.1 p.2) ⁻¹' Iic y) volume := by
    intro y
    have hpre : (fun p : I × I => quantile Z p.1 p.2) ⁻¹' Iic y
        = {p : I × I | (p.2 : ℝ) ≤ Z p.1 y} := by
      ext p; exact quantile_le_iff Z hZ p.1 p.2 y
    rw [hpre]
    obtain ⟨g, hgm, hg⟩ := aesm_section Z hZ y
    have hmeas : MeasurableSet {p : I × I | (p.2 : ℝ) ≤ g p.1} :=
      measurableSet_le (measurable_subtype_coe.comp measurable_snd)
        (hgm.measurable.comp measurable_fst)
    refine hmeas.nullMeasurableSet.congr ?_
    have hae : ∀ᵐ p ∂(volume : Measure (I × I)), Z p.1 y = g p.1 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae hg
    filter_upwards [hae] with p hp
    show ((p.2 : ℝ) ≤ g p.1) = ((p.2 : ℝ) ≤ Z p.1 y)
    rw [hp]
  have hm : @Measurable (NullMeasurableSpace (I × I) volume) I _ _
      (fun p : I × I => quantile Z p.1 p.2) := measurable_of_Iic key
  exact fun s hs => hm hs

theorem joint_cdf (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (x y : I) :
    (limitMeasure Z).real (Set.Iic x ×ˢ Set.Iic y) = ∫ t in Set.Iic x, Z t y := by
  have hf : AEMeasurable (fun p : I × I => (p.1, quantile Z p.1 p.2)) volume :=
    measurable_fst.aemeasurable.prodMk (aemeasurable_quantile Z hZ)
  obtain ⟨g, hgm, hg⟩ := aesm_section Z hZ y
  have hmem := hZ.2.1
  have hpre : (fun p : I × I => (p.1, quantile Z p.1 p.2)) ⁻¹' (Iic x ×ˢ Iic y)
      = {p : I × I | p.1 ≤ x ∧ (p.2 : ℝ) ≤ Z p.1 y} := by
    ext p
    simp only [mem_preimage, mem_prod, mem_Iic, mem_ofPred_eq, quantile_le_iff Z hZ]
  have hE' : MeasurableSet {p : I × I | p.1 ≤ x ∧ (p.2 : ℝ) ≤ g p.1} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le (measurable_subtype_coe.comp measurable_snd)
        (hgm.measurable.comp measurable_fst))
  have hae : ∀ᵐ p ∂(volume : Measure (I × I)), Z p.1 y = g p.1 := by
    rw [Measure.volume_eq_prod]; exact Measure.quasiMeasurePreserving_fst.ae hg
  have hEq : volume {p : I × I | p.1 ≤ x ∧ (p.2 : ℝ) ≤ Z p.1 y}
      = volume {p : I × I | p.1 ≤ x ∧ (p.2 : ℝ) ≤ g p.1} := by
    apply measure_congr
    filter_upwards [hae] with p hp
    show (p.1 ≤ x ∧ (p.2 : ℝ) ≤ Z p.1 y) = (p.1 ≤ x ∧ (p.2 : ℝ) ≤ g p.1)
    rw [hp]
  have hvol : ∀ t : I, volume {u : I | (u : ℝ) ≤ Z t y} = ENNReal.ofReal (Z t y) := by
    intro t
    have h : {u : I | (u : ℝ) ≤ Z t y} = Iic (⟨Z t y, hmem t y⟩ : I) := by
      ext u; exact Iff.rfl
    rw [h, volume_Iic]
  calc (limitMeasure Z).real (Set.Iic x ×ˢ Set.Iic y)
      = (volume {p : I × I | p.1 ≤ x ∧ (p.2 : ℝ) ≤ g p.1}).toReal := by
        rw [Measure.real, limitMeasure,
          Measure.map_apply_of_aemeasurable hf (measurableSet_Iic.prod measurableSet_Iic),
          hpre, hEq]
    _ = (∫⁻ t in Iic x, ENNReal.ofReal (Z t y)).toReal := by
        rw [Measure.volume_eq_prod, Measure.prod_apply hE',
          ← lintegral_indicator measurableSet_Iic]
        congr 1
        apply lintegral_congr_ae
        filter_upwards [hg] with t ht
        have ht' : Z t y = g t := ht
        by_cases htx : t ≤ x
        · rw [indicator_of_mem (show t ∈ Iic x from htx), ← hvol t, ht']
          congr 1
          ext u
          simp [htx]
        · rw [indicator_of_notMem (show t ∉ Iic x from htx)]
          have : Prod.mk t ⁻¹' {p : I × I | p.1 ≤ x ∧ (p.2 : ℝ) ≤ g p.1} = ∅ := by
            ext u; simp [htx]
          rw [this, measure_empty]
    _ = ∫ t in Set.Iic x, Z t y := by
        rw [integral_eq_lintegral_of_nonneg_ae]
        · exact Eventually.of_forall fun t => (hmem t y).1
        · exact (aesm_section Z hZ y).restrict

end P577

open PermLimits.Shared MeasureTheory unitInterval in
theorem solution (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (x y : I) :
    (limitMeasure Z).real (Set.Iic x ×ˢ Set.Iic y) = ∫ t in Set.Iic x, Z t y := by
  exact P577.joint_cdf Z hZ x y
