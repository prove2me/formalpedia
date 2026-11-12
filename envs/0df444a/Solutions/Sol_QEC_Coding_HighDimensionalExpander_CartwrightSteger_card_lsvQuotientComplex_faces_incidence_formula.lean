-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_faces_incidence_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:02:37.589977+00:00
-- url     : https://prove2.me/submissions/d9b513f8-ed1a-4388-bc9c-977317136ada

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cayley_face_incidence_formula
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_orderSplitLatticeQuotient


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level p : Nat) :
    p * Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) p) =
      Nat.card
          (OrderSplitCartwrightStegerLattice P r ⧸
            OrderSplitCartwrightStegerCongruenceSubgroup P r level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvQuotientComplex P r level) p //
            1 ∈ σ.vertices} := by
  rw [natCard_orderSplitLatticeQuotient P r level]
  change p * Fintype.card
      (SimplicialChain.Face
        (CayleyClique.cayleyCliqueComplex
          (indexColoredGeneratorFinset P r level :
            Set (IndexFiniteGroup P r level))) p) =
    Nat.card (IndexFiniteGroup P r level) *
      Fintype.card
        {σ : SimplicialChain.Face
            (CayleyClique.cayleyCliqueComplex
              (indexColoredGeneratorFinset P r level :
                Set (IndexFiniteGroup P r level))) p //
          1 ∈ σ.vertices}
  rw [Nat.card_eq_fintype_card]
  exact cayley_face_incidence_formula
    (indexColoredGeneratorFinset P r level :
      Set (IndexFiniteGroup P r level)) p
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
