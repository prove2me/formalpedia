-- Prove2me | solution 1 for P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:34.013183+00:00
-- url     : https://prove2.me/submissions/7d21e6e1-aef8-422b-b865-3dc5254fcf9f

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_uniformizer
import Theorems.Thm_GroundTheory_FunctionField_Place_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_valuation_algebraMap
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_exp_neg_ord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
variable [IsFunctionField k K]
variable [IsFunctionField k K']
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    (IsLocalRing.maximalIdeal v.ring).ramificationIdx' (IsLocalRing.maximalIdeal w.ring) =
      w.ramificationIdx v := by
  let := h.algebra
  have h1 := h.valuation_algebraMap v.uniformizer
  have hπ : algebraMap K K' v.uniformizer ≠ 0 := (map_ne_zero _).2 v.uniformizer_ne_zero
  rw [v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    w.valuation_eq_exp_neg_ord hπ, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
  rw [ramificationIdx]
  omega
end LiesOver
end GroundTheory.FunctionField.Place
