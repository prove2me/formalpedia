-- Prove2me | solution 1 for TunnellMap.etaPoint_neg_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:41.727898+00:00
-- url     : https://prove2.me/submissions/e67fd37d-c876-4529-bfb6-a2827300136e

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_minusVector_ne_zero
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_ne_zero
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plus_minus_keys_ne
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_source



set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint (negBResidual s) t = - etaPoint s t := by
  unfold etaPoint
  rw [plusVector_neg_source, minusVector_neg_source,
    directionKey_negTriple (minusVector_ne_zero s t),
    directionKey_negTriple (plusVector_ne_zero s t)]
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · have h' : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (plus_minus_keys_ne s t))
    rw [if_pos h', if_neg h]
    norm_num
end TunnellMap
