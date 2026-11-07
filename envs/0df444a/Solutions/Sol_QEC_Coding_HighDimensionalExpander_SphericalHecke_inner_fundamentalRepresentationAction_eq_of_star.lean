-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_eq_of_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:07.623205+00:00
-- url     : https://prove2.me/submissions/a5caa139-69ec-4dca-8fb2-c893afa39944

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_integratedHeckeAction_eq_star

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
    (hd : 0 < d) (r s : ℕ)
    (hstar : star (HeckeFunction.fundamentalHeckeFunction k d r) =
      HeckeFunction.fundamentalHeckeFunction k d s)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous r v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous s w) := by
  change inner ℂ
      (integratedHeckeAction rho
        (HeckeFunction.fundamentalHeckeFunction k d r) v) w =
    inner ℂ v
      (integratedHeckeAction rho
        (HeckeFunction.fundamentalHeckeFunction k d s) w)
  rw [← hstar]
  exact inner_integratedHeckeAction_eq_star
    rho hcontinuous hunitary hd _ v w
end QEC.Coding.HighDimensionalExpander.SphericalHecke
