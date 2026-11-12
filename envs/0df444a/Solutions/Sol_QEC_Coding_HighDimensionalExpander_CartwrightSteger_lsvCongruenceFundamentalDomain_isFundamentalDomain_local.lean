-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvCongruenceFundamentalDomain_isFundamentalDomain_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:08:44.859249+00:00
-- url     : https://prove2.me/submissions/5dabaf8c-d5d1-466d-9a8e-cbdc56a624db

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
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsFundamentalDomain
      (lsvLocalCongruenceSubgroup P r level)
      (lsvCongruenceFundamentalDomain P r level)
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) := by
  apply IsFundamentalDomain.mk'
  · exact (measurableSet_lsvCongruenceFundamentalDomain P r level).nullMeasurableSet
  · exact existsUnique_localCongruence_mul_mem_lsvFundamentalDomain P r level
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
