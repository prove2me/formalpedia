-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeAction_eq_eigenvalue_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:03.818677+00:00
-- url     : https://prove2.me/submissions/b0ffc088-8a64-40f6-95c5-0f1325715578

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeActionContinuousLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeAction_mem_kFixedSubmodule
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
    (hline : Module.finrank ℂ (kFixedSubmodule rho) = 1)
    (f : HeckeFunction k d) (v : V)
    (hvfixed : v ∈ kFixedSubmodule rho) (hvnorm : ‖v‖ = 1) :
    integratedHeckeActionLinear rho hcontinuous f v =
      sphericalHeckeEigenvalue rho hcontinuous f v • v := by
  have hvzero : v ≠ 0 := by
    intro hv
    simp [hv] at hvnorm
  let vK : kFixedSubmodule rho := ⟨v, hvfixed⟩
  let AvK : kFixedSubmodule rho :=
    ⟨integratedHeckeActionLinear rho hcontinuous f v,
      integratedHeckeAction_mem_kFixedSubmodule rho hcontinuous hunitary f v⟩
  have hvKzero : vK ≠ 0 := by
    intro h
    apply hvzero
    exact Subtype.ext_iff.mp h
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hvKzero AvK
  have haction : integratedHeckeActionLinear rho hcontinuous f v = c • v := by
    exact congrArg Subtype.val hc.symm
  rw [haction]
  have hinner : inner ℂ v (c • v) = c := by
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm]
  simp only [sphericalHeckeEigenvalue, haction, hinner]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
