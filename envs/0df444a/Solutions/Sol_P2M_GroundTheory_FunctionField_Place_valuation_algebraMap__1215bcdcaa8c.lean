-- Prove2me | solution 1 for P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:29.839093+00:00
-- url     : https://prove2.me/submissions/60416b28-4c03-4ca0-8480-21c8ce36c65a

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_isEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution {c : k} (hc : c ≠ 0) : v.valuation (algebraMap k K c) = 1 :=
  v.valuation_isEquiv.eq_one_iff_eq_one.2 (v.valuation_algebraMap hc)
end GroundTheory.FunctionField.Place
