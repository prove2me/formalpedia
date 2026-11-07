-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_rankFour_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:07:57.21753+00:00
-- url     : https://prove2.me/submissions/47a34a47-9ab8-448d-bbed-533ba309a127

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_fundamentalRepresentationAction_eq_of_star
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory
open scoped ComplexConjugate MatrixGroups LocalTopology
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 4) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 2 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 2 w) :=
  inner_fundamentalRepresentationAction_eq_of_star
    rho hcontinuous hunitary (by omega) 2 2
      (HeckeFunction.star_fundamentalHeckeFunction_rankFour_two k) v w
end QEC.Coding.HighDimensionalExpander.SphericalHecke
