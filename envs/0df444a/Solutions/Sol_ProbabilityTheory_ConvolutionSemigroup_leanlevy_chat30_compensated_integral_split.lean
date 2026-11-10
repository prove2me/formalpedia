-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_compensated_integral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:37:49.979979+00:00
-- url     : https://prove2.me/submissions/0c659a83-c33b-4d79-997c-72cb635705c4

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

open ProbabilityTheory.ConvolutionSemigroup

/-- Source-exact partition of the compensated Lévy exponent into a small ball, annulus,
and outer tail; this is the fourth identity in the pinned upstream ψ-algebra proof. -/
theorem solution
    {r : ℝ} (hr : r ∈ Set.Ioc (1/2 : ℝ) 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    (∫ x, levyCompensatedIntegrand ξ x ∂ν)
      = (∫ x in {x : ℝ | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν)
        + (∫ x in {x : ℝ | r ≤ |x| ∧ |x| < 1},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν)
        + (∫ x in largeSet 1, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν) := by
  set Bball : Set ℝ := {x | |x| < r} with hBball_def
  set Bband : Set ℝ := {x | r ≤ |x| ∧ |x| < 1} with hBband_def
  have hr1 : r ≤ 1 := hr.2
  have hmeas_small : MeasurableSet smallSet :=
    (isOpen_Iio.preimage continuous_abs).measurableSet
  have hmeas_ball : MeasurableSet Bball :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hmeas_band : MeasurableSet Bband :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hmeas_ge1 : MeasurableSet (largeSet 1) :=
    (isClosed_Ici.preimage continuous_abs).measurableSet
  have hlevy_small : ∀ x : ℝ, |x| < 1 →
      levyCompensatedIntegrand ξ x =
        exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I := by
    intro x hx
    simp [levyCompensatedIntegrand, hx]
  have hlevy_large : ∀ x : ℝ, x ∈ largeSet 1 →
      levyCompensatedIntegrand ξ x = exp ((↑x : ℂ) * ↑ξ * I) - 1 := by
    intro x hx
    simp [levyCompensatedIntegrand, show ¬(|x| < 1) from
      not_lt.mpr (show 1 ≤ |x| from hx)]
  have hcomp_ball : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) Bball ν := by
    refine ((integrable_levyCompensatedIntegrand hν ξ).integrableOn).congr ?_
    filter_upwards [ae_restrict_mem hmeas_ball] with x hx
    exact hlevy_small x (lt_of_lt_of_le hx hr1)
  have hcomp_band : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) Bband ν := by
    refine ((integrable_levyCompensatedIntegrand hν ξ).integrableOn).congr ?_
    filter_upwards [ae_restrict_mem hmeas_band] with x hx
    exact hlevy_small x hx.2
  have hsplit_top : (∫ x, levyCompensatedIntegrand ξ x ∂ν)
      = (∫ x in smallSet, levyCompensatedIntegrand ξ x ∂ν)
        + ∫ x in (smallSet)ᶜ, levyCompensatedIntegrand ξ x ∂ν :=
    (integral_add_compl hmeas_small (integrable_levyCompensatedIntegrand hν ξ)).symm
  have hcompl_small : (smallSet : Set ℝ)ᶜ = largeSet 1 := by
    ext x
    simp [smallSet, largeSet, not_lt]
  have hlarge : (∫ x in (smallSet)ᶜ, levyCompensatedIntegrand ξ x ∂ν)
      = ∫ x in largeSet 1, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν := by
    rw [hcompl_small]
    exact setIntegral_congr_fun hmeas_ge1 (fun x hx => hlevy_large x hx)
  have hsmall : (∫ x in smallSet, levyCompensatedIntegrand ξ x ∂ν)
      = (∫ x in Bball, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν)
        + (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν) := by
    have h_disj : Disjoint Bball Bband := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx'.1 (not_le.mpr hx)
    have h_union : (smallSet : Set ℝ) = Bball ∪ Bband := by
      ext x
      simp only [smallSet, hBball_def, hBband_def, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hx
        rcases lt_or_ge (|x|) r with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hx⟩
      · rintro (h | ⟨_, h⟩)
        · exact lt_of_lt_of_le h hr1
        · exact h
    have hrw : (∫ x in smallSet, levyCompensatedIntegrand ξ x ∂ν)
        = ∫ x in smallSet, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν :=
      setIntegral_congr_fun hmeas_small (fun x hx => hlevy_small x hx)
    rw [hrw, h_union, setIntegral_union h_disj hmeas_band hcomp_ball hcomp_band]
  rw [hsplit_top, hlarge, hsmall]
