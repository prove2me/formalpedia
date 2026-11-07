-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:38.246378+00:00
-- url     : https://prove2.me/submissions/4a9d9147-ba57-4e80-92b2-386deae6ea6a

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_reducedMatrix_rows_independent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20 QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]
namespace QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
theorem _root_.solution
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Function.Surjective (reducedBoundary Y) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hRank : (reducedMatrix Y).rank = Fintype.card (ReducedCheck Y) :=
    (reducedMatrix_rows_independent Y).rank_matrix
  rw [(reducedMatrix Y).rank_eq_finrank_range_toLin
    (Pi.basisFun (ZMod 2) (ReducedCheck Y))
    (Pi.basisFun (ZMod 2) bit)] at hRank
  rw [Matrix.toLin_eq_toLin'] at hRank
  change Module.finrank (ZMod 2) (LinearMap.range (reducedBoundary Y)) =
    Fintype.card (ReducedCheck Y) at hRank
  calc
    Module.finrank (ZMod 2) (LinearMap.range (reducedBoundary Y)) =
        Fintype.card (ReducedCheck Y) := hRank
    _ = Module.finrank (ZMod 2) (Word (ZMod 2) (ReducedCheck Y)) :=
      (Module.finrank_pi (ZMod 2)).symm
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
