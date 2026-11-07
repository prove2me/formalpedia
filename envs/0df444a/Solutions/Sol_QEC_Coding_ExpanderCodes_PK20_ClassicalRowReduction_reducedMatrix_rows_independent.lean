-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedMatrix_rows_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:21.187885+00:00
-- url     : https://prove2.me/submissions/c1bba1ac-5611-47cf-aaaf-f8245f55db30

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_independent_independentRows

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
  LinearIndependent (ZMod 2) (reducedMatrix Y).row := by
  change LinearIndependent (ZMod 2)
    (fun r : ReducedCheck Y => (r.1 : Word (ZMod 2) bit))
  exact linearIndependent_subtype_iff.mpr (independent_independentRows Y)
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
