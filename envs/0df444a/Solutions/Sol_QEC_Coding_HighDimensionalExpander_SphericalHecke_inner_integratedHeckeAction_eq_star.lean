-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_integratedHeckeAction_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:54:02.076896+00:00
-- url     : https://prove2.me/submissions/54d600d2-0350-4825-887a-f35ab7bcf0a1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeActionContinuousLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_isInvInvariant
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeActionContinuousLinear_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory
open scoped ComplexConjugate MatrixGroups LocalTopology
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hd : 0 < d) (f : HeckeFunction k d) (v w : V) :
    inner ℂ (integratedHeckeAction rho f v) w =
      inner ℂ v (integratedHeckeAction rho (star f) w) := by
  letI : MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) :=
    normalizedLocalHaarMeasure_isInvInvariant k hd
  let μ := normalizedLocalHaarMeasure k d
  let F : HeckeGroup k d → V := fun g ↦ f g • rho g v
  let Fstar : HeckeGroup k d → V := fun g ↦ star f g • rho g w
  have hF : Integrable F μ :=
    integrable_integratedHeckeAction rho hcontinuous f v
  have hFstar : Integrable Fstar μ :=
    integrable_integratedHeckeAction rho hcontinuous (star f) w
  have hintegral_left :
      inner ℂ (∫ g, F g ∂μ) w = ∫ g, inner ℂ (F g) w ∂μ := by
    calc
      inner ℂ (∫ g, F g ∂μ) w =
          conj (inner ℂ w (∫ g, F g ∂μ)) := by simp
      _ = conj (∫ g, inner ℂ w (F g) ∂μ) := by
        rw [integral_inner hF w]
      _ = ∫ g, conj (inner ℂ w (F g)) ∂μ := by
        rw [integral_conj]
      _ = ∫ g, inner ℂ (F g) w ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        simp
  have hunit (g : HeckeGroup k d) :
      inner ℂ (rho g⁻¹ v) w = inner ℂ v (rho g w) := by
    have h := hunitary g (rho g⁻¹ v) w
    have hcancel : rho g (rho g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hcancel] at h
    exact h.symm
  change inner ℂ (∫ g, F g ∂μ) w = inner ℂ v (∫ g, Fstar g ∂μ)
  calc
    inner ℂ (∫ g, F g ∂μ) w =
        ∫ g, inner ℂ (F g) w ∂μ := hintegral_left
    _ = ∫ g, inner ℂ (F g⁻¹) w ∂μ :=
      (integral_inv_eq_self (fun g ↦ inner ℂ (F g) w) μ).symm
    _ = ∫ g, inner ℂ v (Fstar g) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      simp only [F, Fstar, HeckeFunction.star_apply]
      rw [inner_smul_left, inner_smul_right, hunit g]
    _ = inner ℂ v (∫ g, Fstar g ∂μ) := integral_inner hFstar v
end QEC.Coding.HighDimensionalExpander.SphericalHecke
