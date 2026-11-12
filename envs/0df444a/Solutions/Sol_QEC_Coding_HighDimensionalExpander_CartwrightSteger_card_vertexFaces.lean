-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_vertexFaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:31:53.252779+00:00
-- url     : https://prove2.me/submissions/0afd76af-cdc8-4b31-bfa7-44ba1934735a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)
omit [DecidableEq V]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution :
    Fintype.card (SimplicialChain.Face K 1) = Fintype.card V :=
  Fintype.card_congr (vertexFaceEquiv K)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
