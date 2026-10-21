-- Prove2me | solution 1 for PermLimits.Cauchy.supDist_le_rectDist_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T11:08:51.073699+00:00
-- url     : https://prove2.me/submissions/c20c7e45-9483-4699-883d-5667bb413148

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_RectDist
import Definitions.Def_PermLimits_Cauchy_SupDist

set_option autoImplicit false

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

open PermLimits.Shared PermLimits.Cauchy unitInterval in
theorem solution (Z₁ Z₂ : I → I → ℝ) (hZ₁ : IsLimitPerm Z₁) (hZ₂ : IsLimitPerm Z₂) :
    supDist Z₁ Z₂ ≤ rectDist Z₁ Z₂ ∧ rectDist Z₁ Z₂ ≤ 4 * supDist Z₁ Z₂ := by
  exact P734.main Z₁ Z₂ hZ₁ hZ₂
