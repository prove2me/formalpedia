-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeActionContinuousLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:26:08.823284+00:00
-- url     : https://prove2.me/submissions/54864435-f79a-449f-ae14-caa648f4a0cb

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation

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
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) (v : V) :
    integratedHeckeActionContinuousLinear rho hcontinuous hunitary f v =
      integratedHeckeAction rho f v :=
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
