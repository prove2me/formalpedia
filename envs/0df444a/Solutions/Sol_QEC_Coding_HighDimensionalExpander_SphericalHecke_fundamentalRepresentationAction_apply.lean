-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalRepresentationAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:07:35.646199+00:00
-- url     : https://prove2.me/submissions/fccbc06b-c89d-4c74-912c-8eb860136448

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_isOpen
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
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (r : ℕ) (v : V) :
    fundamentalRepresentationAction rho hcontinuous r v =
      ∫ g in fundamentalDoubleCoset k d r, rho g v
        ∂(normalizedLocalHaarMeasure k d) := by
  change (∫ g, (fundamentalDoubleCoset k d r).indicator (fun _ ↦ (1 : ℂ)) g •
      rho g v ∂(normalizedLocalHaarMeasure k d)) = _
  have hfun : (fun g : HeckeGroup k d ↦
      (fundamentalDoubleCoset k d r).indicator (fun _ ↦ (1 : ℂ)) g • rho g v) =
      (fundamentalDoubleCoset k d r).indicator (fun g ↦ rho g v) := by
    funext g
    by_cases hg : g ∈ fundamentalDoubleCoset k d r <;> simp [hg]
  calc
    (∫ g, (fundamentalDoubleCoset k d r).indicator (fun _ ↦ (1 : ℂ)) g •
        rho g v ∂(normalizedLocalHaarMeasure k d)) =
        ∫ g, (fundamentalDoubleCoset k d r).indicator (fun g ↦ rho g v) g
          ∂(normalizedLocalHaarMeasure k d) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun g ↦ congrFun hfun g)
    _ = ∫ g in fundamentalDoubleCoset k d r, rho g v
          ∂(normalizedLocalHaarMeasure k d) := by
      rw [integral_indicator]
      exact (fundamentalDoubleCoset_isOpen k d r).measurableSet
end QEC.Coding.HighDimensionalExpander.SphericalHecke
