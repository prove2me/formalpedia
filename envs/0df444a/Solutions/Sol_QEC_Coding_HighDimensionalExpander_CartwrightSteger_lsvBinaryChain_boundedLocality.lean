-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBinaryChain_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:03:28.996094+00:00
-- url     : https://prove2.me/submissions/9f880cc3-ef5d-462c-88f4-219b24e3bdec

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_cofaces_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_boundedLocality_of_coface_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level p : Nat) (hp : 1 ≤ p) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (lsvBinaryChainAt P r level p)).localityProfile
      (max (max (2 * indexColoredGeneratorBound P r) (p + 2))
        (p + 1 + 2 * indexColoredGeneratorBound P r)) := by
  apply SimplicialChain.boundedLocality_of_coface_bounds
    (lsvQuotientComplex P r level) p
      (2 * indexColoredGeneratorBound P r) hp
  · exact fun σ => card_lsvQuotientComplex_cofaces_le P r level p σ
  · exact fun τ => card_lsvQuotientComplex_cofaces_le P r level (p + 1) τ
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
