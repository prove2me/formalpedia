-- Prove2me | solution 1 for TunnellMap.etaPoint_neg_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:21.034801+00:00
-- url     : https://prove2.me/submissions/95cea570-8faf-47fb-8b86-e64c37b9a822

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_plus_minus_keys_ne
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_target



set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s (negAResidual t) = - etaPoint s t := by
  unfold etaPoint
  rw [plusVector_neg_target, minusVector_neg_target]
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · have h' : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (plus_minus_keys_ne s t))
    rw [if_pos h', if_neg h]
    norm_num
end TunnellMap
