-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvRightRegularRepresentation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:00:29.054348+00:00
-- url     : https://prove2.me/submissions/162bd492-20bc-488c-969a-d0fda09c81fb

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.FreeGroup.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open MeasureTheory Set
open scoped ENNReal SphericalHecke.LocalTopology MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : HeckeGroup (BaseField P) r.matrixRank)
    (f : LSVAutomorphicL2 P r level) :
    lsvRightRegularRepresentation P r level g f =
      DomMulAct.mk g⁻¹ • f :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
