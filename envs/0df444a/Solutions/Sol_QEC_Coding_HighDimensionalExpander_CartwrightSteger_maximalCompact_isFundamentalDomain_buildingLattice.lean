-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.maximalCompact_isFundamentalDomain_buildingLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:08:28.110193+00:00
-- url     : https://prove2.me/submissions/51e6caa7-cbe2-4ae9-ac88-74e641bbcb1b

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
    (P : BasePrime) (r : Rank) :
    IsFundamentalDomain
      (BuildingCartwrightStegerLattice P r)
      (maximalCompact (BaseField P) r.matrixRank :
        Set (HeckeGroup (BaseField P) r.matrixRank))
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) := by
  apply IsFundamentalDomain.mk'
  · exact (maximalCompact_isOpen (BaseField P) r.matrixRank).measurableSet.nullMeasurableSet
  · exact existsUnique_buildingLattice_mul_mem_maximalCompact P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
