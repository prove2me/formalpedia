-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.card_reducedCheck_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:29.982904+00:00
-- url     : https://prove2.me/submissions/2de4a4fc-b2ba-4e61-97d7-48aed9d70ea0

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_originalRow_injective

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
    Fintype.card (ReducedCheck Y) ≤ Fintype.card check := by
  exact Fintype.card_le_of_injective (originalRow Y)
    (originalRow_injective Y)
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
