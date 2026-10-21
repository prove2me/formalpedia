-- Prove2me | solution 1 for PermLimits.Cauchy.convergences_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T12:21:33.759378+00:00
-- url     : https://prove2.me/submissions/2d5e4013-3a35-41b7-a951-9b6495099ab1

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_RectDist
import Definitions.Def_PermLimits_Shared_LimitConvergence
import Definitions.Def_PermLimits_Cauchy_SupDist
import Theorems.Thm_PermLimits_Existence_weak_conv_iff_uniform_cdf
import Theorems.Thm_PermLimits_Existence_densities_determine_measure

/-!
Lemma 5.3 of Hoppen et al. (arXiv:1103.5844v2): the three convergences of limit permutations agree.
Reduction to Lemma 2.1 (`PermLimits.Existence.weak_conv_iff_uniform_cdf`) and Lemma 5.1
(`PermLimits.Existence.densities_determine_measure`); Eq. (21), Eq. (34), Lemma 2.2(a), the
continuous-mapping step and the compactness step are proved below.
-/

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

namespace P734

open PermLimits.Shared PermLimits.Cauchy MeasureTheory unitInterval Filter Topology Set

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

theorem integ (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (y : I) :
    Integrable (fun t => Z t y) volume := by
  refine Integrable.of_bound (aesm_section Z hZ y) 1 (Eventually.of_forall fun t => ?_)
  have h := hZ.2.1 t y
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

theorem F_mem (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (y : I) (s : Set I) :
    0 ≤ ∫ t in s, Z t y ∧ ∫ t in s, Z t y ≤ (y : ℝ) := by
  have hnn : 0 ≤ᵐ[(volume : Measure I)] fun t => Z t y :=
    Eventually.of_forall fun t => (hZ.2.1 t y).1
  refine ⟨integral_nonneg fun t => (hZ.2.1 t y).1, ?_⟩
  · rw [← hZ.2.2.2 y]
    exact setIntegral_le_integral (integ Z hZ y) hnn

theorem F_zero (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (s : Set I) :
    ∫ t in s, Z t 0 = 0 := by
  have h := F_mem Z hZ 0 s
  have h0 : ((0 : I) : ℝ) = 0 := rfl
  rw [h0] at h
  exact le_antisymm h.2 h.1

theorem split (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (y : I) (a b : I) (hab : a ≤ b) :
    ∫ t in Icc a b, Z t y = (∫ t in Iic b, Z t y) - ∫ t in Iic a, Z t y := by
  have hi := integ Z hZ y
  have h1 : ∫ t in Icc a b, Z t y = ∫ t in Ioc a b, Z t y :=
    (setIntegral_congr_set Ioc_ae_eq_Icc).symm
  rw [h1, ← Iic_union_Ioc_eq_Iic hab,
    setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hi.integrableOn
      hi.integrableOn]
  ring

theorem sup_bdd (Z₁ Z₂ : I → I → ℝ) (hZ₁ : IsLimitPerm Z₁) (hZ₂ : IsLimitPerm Z₂) :
    BddAbove {r : ℝ | ∃ x y : I,
      r = |(∫ t in Set.Iic x, Z₁ t y) - (∫ t in Set.Iic x, Z₂ t y)|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, y, rfl⟩
  have h1 := F_mem Z₁ hZ₁ y (Iic x)
  have h2 := F_mem Z₂ hZ₂ y (Iic x)
  have hy := y.2.2
  rw [abs_le]; constructor <;> linarith

theorem rect_bdd (Z₁ Z₂ : I → I → ℝ) (hZ₁ : IsLimitPerm Z₁) (hZ₂ : IsLimitPerm Z₂) :
    BddAbove {r : ℝ | ∃ x₁ x₂ y₁ y₂ : I, x₁ < x₂ ∧ y₁ < y₂ ∧
    r = |(∫ x in Set.Icc x₁ x₂, (Z₁ x y₂ - Z₁ x y₁)) -
          (∫ x in Set.Icc x₁ x₂, (Z₂ x y₂ - Z₂ x y₁))|} := by
  refine ⟨2, ?_⟩
  rintro r ⟨x₁, x₂, y₁, y₂, -, -, rfl⟩
  rw [integral_sub (integ Z₁ hZ₁ y₂).integrableOn (integ Z₁ hZ₁ y₁).integrableOn,
    integral_sub (integ Z₂ hZ₂ y₂).integrableOn (integ Z₂ hZ₂ y₁).integrableOn]
  have a1 := F_mem Z₁ hZ₁ y₂ (Icc x₁ x₂)
  have a2 := F_mem Z₁ hZ₁ y₁ (Icc x₁ x₂)
  have a3 := F_mem Z₂ hZ₂ y₂ (Icc x₁ x₂)
  have a4 := F_mem Z₂ hZ₂ y₁ (Icc x₁ x₂)
  have h1 := y₁.2.2
  have h2 := y₂.2.2
  rw [abs_le]; constructor <;> linarith

theorem main (Z₁ Z₂ : I → I → ℝ) (hZ₁ : IsLimitPerm Z₁) (hZ₂ : IsLimitPerm Z₂) :
    supDist Z₁ Z₂ ≤ rectDist Z₁ Z₂ ∧ rectDist Z₁ Z₂ ≤ 4 * supDist Z₁ Z₂ := by
  have hSb := sup_bdd Z₁ Z₂ hZ₁ hZ₂
  have hRb := rect_bdd Z₁ Z₂ hZ₁ hZ₂
  have h01 : (0 : I) < 1 := by
    show ((0 : I) : ℝ) < ((1 : I) : ℝ)
    norm_num
  have hRne : (rectDist Z₁ Z₂) ≥ 0 :=
    (abs_nonneg _).trans (le_csSup hRb ⟨0, 1, 0, 1, h01, h01, rfl⟩)
  have hS : ∀ x y : I, |(∫ t in Set.Iic x, Z₁ t y) - (∫ t in Set.Iic x, Z₂ t y)| ≤
      supDist Z₁ Z₂ := fun x y => le_csSup hSb ⟨x, y, rfl⟩
  constructor
  · unfold supDist
    refine csSup_le ⟨_, 0, 0, rfl⟩ ?_
    rintro r ⟨x, y, rfl⟩
    rcases eq_or_lt_of_le (unitInterval.nonneg' : (0 : I) ≤ x) with hx | hx
    · subst hx
      have hz : (volume : Measure I) (Iic 0) = 0 := by
        rw [volume_Iic]; simp
      rw [setIntegral_measure_zero _ hz, setIntegral_measure_zero _ hz, sub_zero, abs_zero]
      exact hRne
    rcases eq_or_lt_of_le (unitInterval.nonneg' : (0 : I) ≤ y) with hy | hy
    · subst hy
      rw [F_zero Z₁ hZ₁, F_zero Z₂ hZ₂, sub_zero, abs_zero]
      exact hRne
    refine le_csSup hRb ⟨0, x, 0, y, hx, hy, ?_⟩
    have hI : Icc (0 : I) x = Iic x := by
      ext t; exact ⟨fun h => h.2, fun h => ⟨unitInterval.nonneg', h⟩⟩
    rw [hI, integral_sub (integ Z₁ hZ₁ y).integrableOn (integ Z₁ hZ₁ 0).integrableOn,
      integral_sub (integ Z₂ hZ₂ y).integrableOn (integ Z₂ hZ₂ 0).integrableOn,
      F_zero Z₁ hZ₁, F_zero Z₂ hZ₂, sub_zero, sub_zero]
  · unfold rectDist
    refine csSup_le ⟨_, 0, 1, 0, 1, h01, h01, rfl⟩ ?_
    rintro r ⟨x₁, x₂, y₁, y₂, hx, -, rfl⟩
    rw [integral_sub (integ Z₁ hZ₁ y₂).integrableOn (integ Z₁ hZ₁ y₁).integrableOn,
      integral_sub (integ Z₂ hZ₂ y₂).integrableOn (integ Z₂ hZ₂ y₁).integrableOn,
      split Z₁ hZ₁ y₂ x₁ x₂ hx.le, split Z₁ hZ₁ y₁ x₁ x₂ hx.le,
      split Z₂ hZ₂ y₂ x₁ x₂ hx.le, split Z₂ hZ₂ y₁ x₁ x₂ hx.le]
    have e1 := abs_le.1 (hS x₂ y₂)
    have e2 := abs_le.1 (hS x₁ y₂)
    have e3 := abs_le.1 (hS x₂ y₁)
    have e4 := abs_le.1 (hS x₁ y₁)
    rw [abs_le]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

end P734

namespace P021

open PermLimits.Shared PermLimits.Cauchy MeasureTheory ProbabilityTheory unitInterval Filter Topology Set

/-- Eq. (21) (577af9b8). -/
def H21 : Prop := ∀ (Z : I → I → ℝ), IsLimitPerm Z → ∀ x y : I,
  (limitMeasure Z).real (Set.Iic x ×ˢ Set.Iic y) = ∫ t in Set.Iic x, Z t y

/-- Eq. (34) (734e010a). -/
def H34 : Prop := ∀ (Z₁ Z₂ : I → I → ℝ), IsLimitPerm Z₁ → IsLimitPerm Z₂ →
  supDist Z₁ Z₂ ≤ rectDist Z₁ Z₂ ∧ rectDist Z₁ Z₂ ≤ 4 * supDist Z₁ Z₂

/-- boundedness of the supDist set (P734.sup_bdd). -/
def HB : Prop := ∀ (Z₁ Z₂ : I → I → ℝ), IsLimitPerm Z₁ → IsLimitPerm Z₂ →
  BddAbove {r : ℝ | ∃ x y : I,
      r = |(∫ t in Set.Iic x, Z₁ t y) - (∫ t in Set.Iic x, Z₂ t y)|}

/-- Lemma 2.1 (b3a64650). -/
def L21 : Prop := ∀ (μs : ℕ → Measure (I × I)) (μ : Measure (I × I)),
    (∀ n, IsProbabilityMeasure (μs n)) → IsProbabilityMeasure μ →
    (∀ n, (μs n).map Prod.fst = volume) → (∀ n, (μs n).map Prod.snd = volume) →
    (WeakConvMeasures μs μ ↔
      TendstoUniformly (fun n (p : I × I) => jointCDF (μs n) p.1 p.2)
        (fun p : I × I => jointCDF μ p.1 p.2) atTop)

lemma Iic_one : Set.Iic (1 : I) = Set.univ := by
  ext x; simp only [Set.mem_Iic, Set.mem_univ, iff_true]; exact x.2.2

lemma isProb (h21 : H21) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    IsProbabilityMeasure (limitMeasure Z) := by
  have h := h21 Z hZ 1 1
  have h1 : ∫ t in Set.Iic (1 : I), Z t 1 = 1 := by
    have : (fun t => Z t 1) = fun _ => (1 : ℝ) := funext fun t => (hZ.2.2.1 t).2.2.2
    rw [this, Iic_one, Measure.restrict_univ]; simp
  rw [h1, Iic_one, Set.univ_prod_univ] at h
  constructor
  rw [Measure.real, ENNReal.toReal_eq_one_iff] at h
  exact h

lemma real_Iic (x : I) : (volume : Measure I).real (Set.Iic x) = (x : ℝ) := by
  rw [Measure.real, volume_Iic, ENNReal.toReal_ofReal x.2.1]

lemma marg_fst (h21 : H21) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    (limitMeasure Z).map Prod.fst = volume := by
  have := isProb h21 Z hZ
  have : IsProbabilityMeasure ((limitMeasure Z).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply measurable_fst measurableSet_Iic]
  have hpre : Prod.fst ⁻¹' Set.Iic x = Set.Iic x ×ˢ Set.Iic (1 : I) := by
    rw [Iic_one, Set.prod_univ]
  rw [hpre]
  have h := h21 Z hZ x 1
  have h1 : ∫ t in Set.Iic x, Z t 1 = (volume : Measure I).real (Set.Iic x) := by
    have : (fun t => Z t 1) = fun _ => (1 : ℝ) := funext fun t => (hZ.2.2.1 t).2.2.2
    rw [this]; simp
  rw [h1] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← ENNReal.ofReal_toReal
    (measure_ne_top (volume : Measure I) (Set.Iic x))]
  exact congrArg ENNReal.ofReal h

lemma marg_snd (h21 : H21) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    (limitMeasure Z).map Prod.snd = volume := by
  have := isProb h21 Z hZ
  have : IsProbabilityMeasure ((limitMeasure Z).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply measurable_snd measurableSet_Iic]
  have hpre : Prod.snd ⁻¹' Set.Iic y = Set.Iic (1 : I) ×ˢ Set.Iic y := by
    rw [Iic_one, Set.univ_prod]
  rw [hpre]
  have h := h21 Z hZ 1 y
  rw [Iic_one, Measure.restrict_univ, hZ.2.2.2 y, ← real_Iic y] at h
  rw [← Iic_one] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← ENNReal.ofReal_toReal
    (measure_ne_top (volume : Measure I) (Set.Iic y))]
  exact congrArg ENNReal.ofReal h

/-- C1: `Z_n ⇒ Z ↔ Z_n →□ Z`. -/
theorem C1 (h21 : H21) (h34 : H34) (hb : HB) (l21 : L21)
    (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) :
    WeakConv Zs Z ↔ RectConv Zs Z := by
  have := isProb h21 Z hZ
  have hW := l21 (fun n => limitMeasure (Zs n)) (limitMeasure Z)
    (fun n => isProb h21 (Zs n) (hZs n)) (isProb h21 Z hZ)
    (fun n => marg_fst h21 (Zs n) (hZs n)) (fun n => marg_snd h21 (Zs n) (hZs n))
  unfold WeakConv
  rw [hW]
  have hF : ∀ (W : I → I → ℝ), IsLimitPerm W → ∀ p : I × I,
      jointCDF (limitMeasure W) p.1 p.2 = ∫ t in Set.Iic p.1, W t p.2 :=
    fun W hW p => h21 W hW p.1 p.2
  have hTU : TendstoUniformly (fun n (p : I × I) => jointCDF (limitMeasure (Zs n)) p.1 p.2)
        (fun p : I × I => jointCDF (limitMeasure Z) p.1 p.2) atTop ↔
      Tendsto (fun n => supDist (Zs n) Z) atTop (𝓝 0) := by
    rw [Metric.tendstoUniformly_iff]
    simp only [hF _ (hZs _), hF _ hZ, Real.dist_eq]
    constructor
    · intro h
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 (h (ε / 2) (by linarith))
      refine ⟨N, fun n hn => ?_⟩
      have hle : supDist (Zs n) Z ≤ ε / 2 := by
        unfold supDist
        refine csSup_le ⟨_, 0, 0, rfl⟩ ?_
        rintro r ⟨x, y, rfl⟩
        rw [abs_sub_comm]; exact (hN n hn (x, y)).le
      have h0 : 0 ≤ supDist (Zs n) Z := by
        unfold supDist
        exact le_csSup_of_le (hb _ _ (hZs n) hZ) ⟨0, 0, rfl⟩ (abs_nonneg _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
      linarith
    · intro h ε hε
      filter_upwards [(tendsto_order.1 h).2 ε hε] with n hn p
      have hle : |(∫ t in Set.Iic p.1, Zs n t p.2) - ∫ t in Set.Iic p.1, Z t p.2|
          ≤ supDist (Zs n) Z := by
        unfold supDist
        exact le_csSup (hb _ _ (hZs n) hZ) ⟨p.1, p.2, rfl⟩
      rw [abs_sub_comm]; linarith
  rw [hTU]
  unfold RectConv
  constructor
  · intro h
    have hup : Tendsto (fun n => 4 * supDist (Zs n) Z) atTop (𝓝 0) := by
      simpa using h.const_mul 4
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ))) hup
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => (h34 _ _ (hZs n) hZ).2)
    have h0 : 0 ≤ supDist (Zs n) Z := by
      unfold supDist
      exact le_csSup_of_le (hb _ _ (hZs n) hZ) ⟨0, 0, rfl⟩ (abs_nonneg _)
    exact h0.trans (h34 _ _ (hZs n) hZ).1
  · intro h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ))) h
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => (h34 _ _ (hZs n) hZ).1)
    unfold supDist
    exact le_csSup_of_le (hb _ _ (hZs n) hZ) ⟨0, 0, rfl⟩ (abs_nonneg _)


/-! ## C2 -/


/-- tuples with a repeated coordinate -/
def Tie (k : ℕ) : Set (Fin k → I × I) :=
  {p | ∃ a b : Fin k, a ≠ b ∧ ((p a).1 = (p b).1 ∨ (p a).2 = (p b).2)}

def SS {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  {p | (∀ i j, i < j → (p (ρ i)).1 < (p (ρ j)).1) ∧
    ∀ i j, τ i < τ j → (p (ρ i)).2 < (p (ρ j)).2}

def TT {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  {p | (∀ i j, i < j → (p (ρ i)).1 ≤ (p (ρ j)).1) ∧
    ∀ i j, τ i < τ j → (p (ρ i)).2 ≤ (p (ρ j)).2}

lemma SS_sub {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : SS τ ρ ⊆ patternEvent τ := by
  intro p hp
  refine ⟨ρ, hp.1, fun i j => ⟨fun h => ?_, hp.2 i j⟩⟩
  by_contra hn
  rcases lt_or_eq_of_le (not_lt.1 hn) with h2 | h2
  · exact lt_asymm h (hp.2 j i h2)
  · have : j = i := τ.injective h2
    subst this; exact lt_irrefl _ h

lemma sub_SS {k : ℕ} (τ : Equiv.Perm (Fin k)) : patternEvent τ ⊆ ⋃ ρ, SS τ ρ := by
  rintro p ⟨ρ, h1, h2⟩
  exact mem_iUnion.2 ⟨ρ, h1, fun i j h => (h2 i j).2 h⟩

lemma SS_open {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : IsOpen (SS τ ρ) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have h1 : ∀ i j, ∀ᶠ q in 𝓝 p, i < j → (q (ρ i)).1 < (q (ρ j)).1 := by
    intro i j
    by_cases hij : i < j
    · have hc1 : Continuous fun q : Fin k → I × I => (q (ρ i)).1 := by fun_prop
      have hc2 : Continuous fun q : Fin k → I × I => (q (ρ j)).1 := by fun_prop
      exact (hc1.continuousAt.eventually_lt hc2.continuousAt (hp.1 i j hij)).mono
        fun q hq _ => hq
    · exact Eventually.of_forall fun q h => absurd h hij
  have h2 : ∀ i j, ∀ᶠ q in 𝓝 p, τ i < τ j → (q (ρ i)).2 < (q (ρ j)).2 := by
    intro i j
    by_cases hij : τ i < τ j
    · have hc1 : Continuous fun q : Fin k → I × I => (q (ρ i)).2 := by fun_prop
      have hc2 : Continuous fun q : Fin k → I × I => (q (ρ j)).2 := by fun_prop
      exact (hc1.continuousAt.eventually_lt hc2.continuousAt (hp.2 i j hij)).mono
        fun q hq _ => hq
    · exact Eventually.of_forall fun q h => absurd h hij
  exact (eventually_all.2 fun i => eventually_all.2 (h1 i)).and
    (eventually_all.2 fun i => eventually_all.2 (h2 i))

lemma TT_closed {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : IsClosed (TT τ ρ) := by
  have : TT τ ρ = (⋂ i, ⋂ j, ⋂ (_ : i < j),
      {p : Fin k → I × I | (p (ρ i)).1 ≤ (p (ρ j)).1}) ∩
      ⋂ i, ⋂ j, ⋂ (_ : τ i < τ j), {p : Fin k → I × I | (p (ρ i)).2 ≤ (p (ρ j)).2} := by
    ext p; simp [TT]
  rw [this]
  exact IsClosed.inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) (by fun_prop))
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) (by fun_prop))

lemma SS_sub_TT {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : SS τ ρ ⊆ TT τ ρ :=
  fun _ hp => ⟨fun i j h => (hp.1 i j h).le, fun i j h => (hp.2 i j h).le⟩

lemma TT_SS {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) (p : Fin k → I × I) (hT : p ∈ TT τ ρ)
    (hn : p ∉ Tie k) : p ∈ SS τ ρ := by
  have hne : ∀ i j, i ≠ j → (p (ρ i)).1 ≠ (p (ρ j)).1 ∧ (p (ρ i)).2 ≠ (p (ρ j)).2 := by
    intro i j hij
    have hρ : ρ i ≠ ρ j := fun h => hij (ρ.injective h)
    exact ⟨fun h => hn ⟨_, _, hρ, Or.inl h⟩, fun h => hn ⟨_, _, hρ, Or.inr h⟩⟩
  refine ⟨fun i j h => lt_of_le_of_ne (hT.1 i j h) (hne i j h.ne).1,
    fun i j h => lt_of_le_of_ne (hT.2 i j h) (hne i j ?_).2⟩
  rintro rfl; exact lt_irrefl _ h

lemma frontier_sub {k : ℕ} (τ : Equiv.Perm (Fin k)) : frontier (patternEvent τ) ⊆ Tie k := by
  intro p hp
  by_contra hn
  have hcl : closure (patternEvent τ) ⊆ ⋃ ρ, TT τ ρ :=
    closure_minimal ((sub_SS τ).trans (iUnion_mono fun ρ => SS_sub_TT τ ρ))
      (isClosed_iUnion_of_finite fun ρ => TT_closed τ ρ)
  obtain ⟨ρ, hρ⟩ := mem_iUnion.1 (hcl hp.1)
  exact hp.2 (interior_maximal (SS_sub τ ρ) (SS_open τ ρ) (TT_SS τ ρ p hρ hn))

lemma tie_pair_null (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (hX : μ.map Prod.fst = volume) (hY : μ.map Prod.snd = volume) {k : ℕ} (a b : Fin k)
    (hab : a ≠ b) :
    Measure.pi (fun _ : Fin k => μ) {p | (p a).1 = (p b).1 ∨ (p a).2 = (p b).2} = 0 := by
  have hc : ∀ c : I, μ {x | x.1 = c} = 0 ∧ μ {x | x.2 = c} = 0 := by
    intro c
    have h0 : (volume : Measure I) {c} = 0 := measure_singleton c
    constructor
    · rw [← hX, Measure.map_apply measurable_fst (measurableSet_singleton c)] at h0; exact h0
    · rw [← hY, Measure.map_apply measurable_snd (measurableSet_singleton c)] at h0; exact h0
  cases k with
  | zero => exact a.elim0
  | succ n =>
    obtain ⟨b', rfl⟩ := Fin.exists_succAbove_eq hab.symm
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) a
    let Tt : Set ((I × I) × (Fin n → I × I)) :=
      {q | q.1.1 = (q.2 b').1 ∨ q.1.2 = (q.2 b').2}
    have hTm : MeasurableSet Tt :=
      ((isClosed_eq (by fun_prop) (by fun_prop)).union
        (isClosed_eq (by fun_prop) (by fun_prop))).measurableSet
    have hpre : {p : Fin (n + 1) → I × I | (p a).1 = (p (a.succAbove b')).1 ∨
        (p a).2 = (p (a.succAbove b')).2} =
        MeasurableEquiv.piFinSuccAbove (fun _ => I × I) a ⁻¹' Tt := by
      ext p
      simp [Tt, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.removeNth]
    rw [hpre, hmp.measure_preimage hTm.nullMeasurableSet, Measure.prod_apply_symm hTm]
    have hz : ∀ q : Fin n → I × I, μ ((fun x => (x, q)) ⁻¹' Tt) = 0 := by
      intro q
      have hs : (fun x : I × I => (x, q)) ⁻¹' Tt = {x | x.1 = (q b').1} ∪ {x | x.2 = (q b').2} := by
        ext x; simp [Tt]
      rw [hs]; exact measure_union_null (hc _).1 (hc _).2
    simp [hz]

lemma tie_null (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (hX : μ.map Prod.fst = volume) (hY : μ.map Prod.snd = volume) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) (Tie k) = 0 := by
  have : Tie k = ⋃ a, ⋃ b, ⋃ (_ : a ≠ b),
      {p : Fin k → I × I | (p a).1 = (p b).1 ∨ (p a).2 = (p b).2} := by
    ext p; simp [Tie]
  rw [this]
  exact measure_iUnion_null fun a => measure_iUnion_null fun b => measure_iUnion_null
    fun hab => tie_pair_null μ hX hY a b hab

/-- weak convergence of laws implies convergence of pattern densities (C2, general form). -/
theorem C2gen (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) [IsProbabilityMeasure μ]
    (hX : μ.map Prod.fst = volume) (hY : μ.map Prod.snd = volume)
    (hW : WeakConvMeasures μs μ) {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Tendsto (fun n => (Measure.pi fun _ : Fin k => μs n).real (patternEvent τ)) atTop
      (𝓝 ((Measure.pi fun _ : Fin k => μ).real (patternEvent τ))) := by
  let P : ℕ → ProbabilityMeasure (I × I) := fun n => ⟨μs n, hμs n⟩
  let P0 : ProbabilityMeasure (I × I) := ⟨μ, inferInstance⟩
  have hP : Tendsto P atTop (𝓝 P0) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    exact hW f.toContinuousMap
  have hPi : Tendsto (fun n => ProbabilityMeasure.pi (fun _ : Fin k => P n)) atTop
      (𝓝 (ProbabilityMeasure.pi fun _ : Fin k => P0)) :=
    (ProbabilityMeasure.continuous_pi.tendsto _).comp (tendsto_pi_nhds.2 fun _ => hP)
  have hfr : (ProbabilityMeasure.pi fun _ : Fin k => P0) (frontier (patternEvent τ)) = 0 := by
    rw [ProbabilityMeasure.null_iff_toMeasure_null, ProbabilityMeasure.toMeasure_pi]
    exact measure_mono_null (frontier_sub τ) (tie_null μ hX hY k)
  rw [ProbabilityMeasure.null_iff_toMeasure_null] at hfr
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hPi hfr
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp key

/-- C2 for limit permutations: `Z_n ⇒ Z → Z_n →ᵗ Z`. -/
theorem C2 (h21 : H21) (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) (hW : WeakConv Zs Z) :
    DensityConv Zs Z := by
  have := isProb h21 Z hZ
  intro k τ
  exact C2gen _ _ (fun n => isProb h21 (Zs n) (hZs n)) (marg_fst h21 Z hZ) (marg_snd h21 Z hZ)
    hW τ

/-! ## Lemma 2.2(a): a law with uniform marginals comes from a limit permutation -/

/-- Lemma 5.1 (0f8c67fc). -/
def L51 : Prop := ∀ (Z Z' : I → I → ℝ), IsLimitPerm Z → IsLimitPerm Z' →
    (∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), limitDensity τ Z = limitDensity τ Z') →
    limitMeasure Z = limitMeasure Z'

section L22
variable (ν : Measure (I × I)) [IsProbabilityMeasure ν]

/-- `Z(x, y) = P(Y ≤ y | X = x)`, via the conditional kernel. -/
noncomputable def ZK (x y : I) : ℝ := (ν.condKernel x).real (Set.Iic y)

lemma ZK_meas : Measurable (Function.uncurry (ZK ν)) := by
  have hs : MeasurableSet {q : (I × I) × I | q.2 ≤ q.1.2} :=
    measurableSet_le measurable_snd (measurable_snd.comp measurable_fst)
  have h := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight I ν.condKernel) hs
  have : Function.uncurry (ZK ν) = fun a : I × I =>
      ((Kernel.prodMkRight I ν.condKernel) a
        (Prod.mk a ⁻¹' {q : (I × I) × I | q.2 ≤ q.1.2})).toReal := by
    ext ⟨x, y⟩; rfl
  rw [this]; exact h.ennreal_toReal

lemma ZK_mem (x y : I) : ZK ν x y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

lemma ZK_cdf (x : I) : IsCDF (ZK ν x) := by
  refine ⟨fun a b hab => measureReal_mono (Set.Iic_subset_Iic.2 hab), fun y => ?_,
    measureReal_nonneg, ?_⟩
  · let m : Measure ℝ := (ν.condKernel x).map Subtype.val
    have hm : IsProbabilityMeasure m :=
      Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
    have heq : ZK ν x = fun z : I => cdf m (z : ℝ) := by
      funext z
      rw [ProbabilityTheory.cdf_eq_real, Measure.real, Measure.map_apply measurable_subtype_coe measurableSet_Iic]
      have : Subtype.val ⁻¹' Set.Iic (z : ℝ) = Set.Iic z := Set.ext fun t => Iff.rfl
      rw [this]; rfl
    rw [heq]
    exact ((cdf m).right_continuous (y : ℝ)).comp continuous_subtype_val.continuousWithinAt
      (fun z hz => hz)
  · show (ν.condKernel x).real (Set.Iic 1) = 1
    rw [Iic_one]; simp

lemma ZK_int (hX : ν.map Prod.fst = volume) (hY : ν.map Prod.snd = volume) (y : I) :
    ∫ x, ZK ν x y = (y : ℝ) := by
  have hdis := ν.disintegrate ν.condKernel
  have h1 : ν (Set.univ ×ˢ Set.Iic y) =
      ∫⁻ x, ν.condKernel x (Set.Iic y) ∂(volume : Measure I) := by
    conv_lhs => rw [← hdis]
    rw [Measure.compProd_apply_prod MeasurableSet.univ measurableSet_Iic, Measure.restrict_univ,
      show ν.fst = volume from hX]
  have h2 : ν (Set.univ ×ˢ Set.Iic y) = volume (Set.Iic y) := by
    rw [← hY, Measure.map_apply measurable_snd measurableSet_Iic, Set.univ_prod]
  have hmeas : Measurable fun x => ν.condKernel x (Set.Iic y) :=
    ν.condKernel.measurable_coe measurableSet_Iic
  unfold ZK
  simp only [Measure.real]
  rw [integral_toReal hmeas.aemeasurable (Eventually.of_forall fun x => measure_lt_top _ _),
    ← h1, h2, volume_Iic, ENNReal.toReal_ofReal y.2.1]

lemma ZK_joint (hX : ν.map Prod.fst = volume) (x y : I) :
    ν.real (Set.Iic x ×ˢ Set.Iic y) = ∫ t in Set.Iic x, ZK ν t y := by
  have hdis := ν.disintegrate ν.condKernel
  have h1 : ν (Set.Iic x ×ˢ Set.Iic y) =
      ∫⁻ t in Set.Iic x, ν.condKernel t (Set.Iic y) ∂(volume : Measure I) := by
    conv_lhs => rw [← hdis]
    rw [Measure.compProd_apply_prod measurableSet_Iic measurableSet_Iic,
      show ν.fst = volume from hX]
  have hmeas : Measurable fun t => ν.condKernel t (Set.Iic y) :=
    ν.condKernel.measurable_coe measurableSet_Iic
  unfold ZK
  simp only [Measure.real]
  rw [integral_toReal hmeas.aemeasurable (Eventually.of_forall fun x => measure_lt_top _ _), ← h1]

theorem L22 (hX : ν.map Prod.fst = volume) (hY : ν.map Prod.snd = volume) :
    IsLimitPerm (ZK ν) :=
  ⟨(ZK_meas ν).aemeasurable, ZK_mem ν, ZK_cdf ν, ZK_int ν hX hY⟩

end L22

/-! ## C3: `Z_n →ᵗ Z → Z_n ⇒ Z` (compactness + Lemma 2.2(a) + C2 + Lemma 5.1) -/

/-- a probability measure as a point of `ProbabilityMeasure`. -/
noncomputable def PM {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : IsProbabilityMeasure μ) :
    ProbabilityMeasure Ω := ⟨μ, h⟩

lemma wc_iff (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) :
    WeakConvMeasures μs μ ↔ Tendsto (fun n => PM (μs n) (hμs n))
      atTop (𝓝 (PM μ hμ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h f; exact h f.toContinuousMap
  · intro h f; exact h (BoundedContinuousFunction.mkOfCompact f)

theorem C3 (h21 : H21) (l21 : L21) (l51 : L51) (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) (hD : DensityConv Zs Z) :
    WeakConv Zs Z := by
  have hP := fun n => isProb h21 (Zs n) (hZs n)
  have hP0 := isProb h21 Z hZ
  unfold WeakConv
  rw [wc_iff _ _ hP hP0]
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq
    (fun n => PM (limitMeasure (Zs (ns n))) (hP (ns n)))
  refine ⟨φ, ?_⟩
  have hQ : Tendsto (fun n => PM (limitMeasure (Zs (ns (φ n)))) (hP _)) atTop (𝓝 ν) := hlim
  have marg : ∀ (g : I × I → I) (hg : Continuous g),
      (∀ n, (limitMeasure (Zs n)).map g = volume) → (ν : Measure (I × I)).map g = volume := by
    intro g hg hm
    have hc := ((ProbabilityMeasure.continuous_map hg).tendsto ν).comp hQ
    have heq : ((fun ν' : ProbabilityMeasure (I × I) => ν'.map hg.measurable.aemeasurable) ∘
        (fun n => PM (limitMeasure (Zs (ns (φ n)))) (hP _))) =
        fun _ => PM (volume : Measure I) inferInstance := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
      exact hm _
    rw [heq] at hc
    have h2 := congrArg (fun q : ProbabilityMeasure I => (q : Measure I))
      (tendsto_nhds_unique hc tendsto_const_nhds)
    have h3 : ((ν.map hg.measurable.aemeasurable : ProbabilityMeasure I) : Measure I) =
        volume := h2
    rwa [ProbabilityMeasure.toMeasure_map] at h3
  have hνp : IsProbabilityMeasure (ν : Measure (I × I)) := inferInstance
  have hX := marg Prod.fst continuous_fst (fun n => marg_fst h21 _ (hZs n))
  have hY := marg Prod.snd continuous_snd (fun n => marg_snd h21 _ (hZs n))
  have hZ' : IsLimitPerm (ZK (ν : Measure (I × I))) := L22 _ hX hY
  have hcdf : ∀ p : I × I, jointCDF (limitMeasure (ZK (ν : Measure (I × I)))) p.1 p.2 =
      jointCDF (ν : Measure (I × I)) p.1 p.2 := by
    intro p; unfold jointCDF; rw [h21 _ hZ' p.1 p.2, ZK_joint _ hX p.1 p.2]
  have hWν : WeakConvMeasures (fun n => limitMeasure (Zs (ns (φ n)))) (ν : Measure (I × I)) :=
    (wc_iff _ _ (fun n => hP _) hνp).2 hQ
  have hW' : WeakConvMeasures (fun n => limitMeasure (Zs (ns (φ n))))
      (limitMeasure (ZK (ν : Measure (I × I)))) := by
    have e1 := l21 (fun n => limitMeasure (Zs (ns (φ n)))) (ν : Measure (I × I)) (fun n => hP _)
      hνp (fun n => marg_fst h21 _ (hZs _)) (fun n => marg_snd h21 _ (hZs _))
    have e2 := l21 (fun n => limitMeasure (Zs (ns (φ n))))
      (limitMeasure (ZK (ν : Measure (I × I)))) (fun n => hP _) (isProb h21 _ hZ')
      (fun n => marg_fst h21 _ (hZs _)) (fun n => marg_snd h21 _ (hZs _))
    rw [e2, funext hcdf]
    exact e1.1 hWν
  have hdens : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
      limitDensity τ Z = limitDensity τ (ZK (ν : Measure (I × I))) := by
    intro k τ
    have := isProb h21 _ hZ'
    have t1 := C2gen (fun n => limitMeasure (Zs (ns (φ n)))) _ (fun n => hP _)
      (marg_fst h21 _ hZ') (marg_snd h21 _ hZ') hW' τ
    have t2 := (hD k τ).comp (hns.comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique t2 t1
  have hEq := l51 Z _ hZ hZ' hdens
  have hfin : WeakConvMeasures (fun n => limitMeasure (Zs (ns (φ n)))) (limitMeasure Z) := by
    rw [hEq]; exact hW'
  exact (wc_iff _ _ (fun n => hP _) hP0).1 hfin

/-- Lemma 5.3 from its ingredients. -/
theorem parent (h21 : H21) (h34 : H34) (hb : HB) (l21 : L21) (l51 : L51)
    (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) :
    (WeakConv Zs Z ↔ RectConv Zs Z) ∧ (RectConv Zs Z ↔ DensityConv Zs Z) := by
  have e := C1 h21 h34 hb l21 Zs Z hZs hZ
  exact ⟨e, fun hR => C2 h21 Zs Z hZs hZ (e.2 hR),
    fun hD => e.1 (C3 h21 l21 l51 Zs Z hZs hZ hD)⟩

end P021

open PermLimits.Shared unitInterval in
theorem solution (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) :
    (WeakConv Zs Z ↔ RectConv Zs Z) ∧ (RectConv Zs Z ↔ DensityConv Zs Z) := by
  exact P021.parent (fun W hW x y => P577.joint_cdf W hW x y)
    (fun Z₁ Z₂ h₁ h₂ => P734.main Z₁ Z₂ h₁ h₂) (fun Z₁ Z₂ h₁ h₂ => P734.sup_bdd Z₁ Z₂ h₁ h₂)
    (fun μs μ hμs hμ hX hY => @PermLimits.Existence.weak_conv_iff_uniform_cdf μs μ hμs hμ hX hY)
    (fun W W' hW hW' h => PermLimits.Existence.densities_determine_measure W W' hW hW' h)
    Zs Z hZs hZ
