-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.classicalDistanceAtLeast_reducedBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:07.406188+00:00
-- url     : https://prove2.me/submissions/29d882c5-ae89-4483-82f5-afa279bc019f

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_ker_reducedBoundary_eq

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
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {d : Nat}
    (hDistance : ClassicalDistanceAtLeast (LinearMap.toMatrix' Y) d) :
    ClassicalDistanceAtLeast
      (LinearMap.toMatrix' (reducedBoundary Y)) d := by
  intro x hx hne
  apply hDistance x
  · rw [Matrix.toLin'_toMatrix'] at hx ⊢
    rw [← LinearMap.mem_ker, ← ker_reducedBoundary_eq Y,
      LinearMap.mem_ker]
    exact hx
  · exact hne
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
