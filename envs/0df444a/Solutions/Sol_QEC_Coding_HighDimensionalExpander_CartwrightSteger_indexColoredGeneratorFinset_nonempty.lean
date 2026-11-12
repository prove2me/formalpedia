-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColoredGeneratorFinset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:59:22.237939+00:00
-- url     : https://prove2.me/submissions/b662866b-159e-41ce-b614-bcc60d856781

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexColorGeneratorFinset_nonempty

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexColoredGeneratorFinset P r level).Nonempty := by
  have hcolor : 1 ∈ Finset.Icc 1 (r.matrixRank - 1) := by
    cases r <;> decide
  obtain ⟨g, hg⟩ := indexColorGeneratorFinset_nonempty P r level 1
  refine ⟨g, ?_⟩
  rw [indexColoredGeneratorFinset, Finset.mem_biUnion]
  exact ⟨1, hcolor, hg⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
