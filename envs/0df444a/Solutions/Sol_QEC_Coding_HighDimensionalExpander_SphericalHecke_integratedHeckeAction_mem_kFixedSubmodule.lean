-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeAction_mem_kFixedSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:03.843017+00:00
-- url     : https://prove2.me/submissions/fbda08a7-64bc-47cb-86c0-fc4b51eaf85b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mem_kFixedSubmodule_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeActionContinuousLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
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
    (f : HeckeFunction k d) (v : V) :
    integratedHeckeAction rho f v ∈ kFixedSubmodule rho := by
  rw [mem_kFixedSubmodule_iff]
  intro h
  let L := actionLinearIsometry rho hunitary (h : HeckeGroup k d)
  let phi : HeckeGroup k d → V := fun g ↦ f g • rho g v
  have hphi : Integrable phi (normalizedLocalHaarMeasure k d) :=
    integrable_integratedHeckeAction rho hcontinuous f v
  change rho (h : HeckeGroup k d)
      (∫ g, phi g ∂(normalizedLocalHaarMeasure k d)) =
    ∫ g, phi g ∂(normalizedLocalHaarMeasure k d)
  calc
    rho (h : HeckeGroup k d)
        (∫ g, phi g ∂(normalizedLocalHaarMeasure k d)) =
        ∫ g, L (phi g) ∂(normalizedLocalHaarMeasure k d) := by
          exact (L.integral_comp_comm phi).symm
    _ = ∫ g, f g • rho ((h : HeckeGroup k d) * g) v
          ∂(normalizedLocalHaarMeasure k d) := by
      apply integral_congr_ae
      filter_upwards with g
      simp only [L, phi, actionLinearIsometry, map_smul]
      change f g • rho (h : HeckeGroup k d) (rho g v) =
        f g • rho ((h : HeckeGroup k d) * g) v
      rw [← Module.End.mul_apply, ← map_mul]
    _ = ∫ g, phi g ∂(normalizedLocalHaarMeasure k d) := by
      let F : HeckeGroup k d → V :=
        fun g ↦ f g • rho ((h : HeckeGroup k d) * g) v
      calc
        (∫ g, f g • rho ((h : HeckeGroup k d) * g) v
            ∂(normalizedLocalHaarMeasure k d)) =
            ∫ g, F ((h : HeckeGroup k d)⁻¹ * g)
              ∂(normalizedLocalHaarMeasure k d) :=
          (integral_mul_left_eq_self F (h : HeckeGroup k d)⁻¹).symm
        _ = ∫ g, phi g ∂(normalizedLocalHaarMeasure k d) := by
          apply integral_congr_ae
          filter_upwards with g
          simp only [F, phi]
          have hf : f ((h : HeckeGroup k d)⁻¹ * g) = f g :=
            f.left_invariant (h : HeckeGroup k d)⁻¹
              ((maximalCompact k d).inv_mem h.property) g
          rw [hf]
          simp
end QEC.Coding.HighDimensionalExpander.SphericalHecke
