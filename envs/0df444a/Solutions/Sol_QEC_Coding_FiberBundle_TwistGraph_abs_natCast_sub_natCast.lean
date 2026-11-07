-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.abs_natCast_sub_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:10.222471+00:00
-- url     : https://prove2.me/submissions/afb87811-126c-47ce-86ab-044798b7eee0

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution (a b : Nat) :
    |(a : Real) - b| = Nat.dist a b := by
  by_cases hab : a ≤ b
  · have habR : (a : Real) ≤ b := by exact_mod_cast hab
    rw [abs_of_nonpos (sub_nonpos.mpr habR)]
    rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab]
    ring
  · have hba : b ≤ a := by omega
    have hbaR : (b : Real) ≤ a := by exact_mod_cast hba
    rw [abs_of_nonneg (sub_nonneg.mpr hbaR)]
    rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba]
end QEC.Coding.FiberBundle.TwistGraph
