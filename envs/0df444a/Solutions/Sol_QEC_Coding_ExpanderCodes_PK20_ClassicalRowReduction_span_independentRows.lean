-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.span_independentRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:22:53.882993+00:00
-- url     : https://prove2.me/submissions/5852acdd-c89a-4a68-9902-512cb3704c36

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction

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
    Submodule.span (ZMod 2)
        (independentRows Y : Set (Word (ZMod 2) bit)) =
      Submodule.span (ZMod 2) (rowSet Y) :=
  (Classical.choose_spec (exists_independentRows Y)).2.1
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
