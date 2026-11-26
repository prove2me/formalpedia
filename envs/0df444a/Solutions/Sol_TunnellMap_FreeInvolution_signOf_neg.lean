-- Prove2me | solution 1 for TunnellMap.FreeInvolution.signOf_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:02.717776+00:00
-- url     : https://prove2.me/submissions/a84b289d-957d-4b36-9fb8-3ba458d2b2c5

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]
namespace TunnellMap.FreeInvolution
theorem _root_.solution (key : X → K) (hkey : Function.Injective key) (x : X) :
    I.signOf key (I.neg x) = - I.signOf key x := by
  have hne : key x ≠ key (I.neg x) := fun h => I.no_fixed x (hkey h).symm
  unfold signOf
  rw [I.neg_neg]
  by_cases h : key x < key (I.neg x)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · have h' : key (I.neg x) < key x := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    rw [if_pos h', if_neg h]; norm_num
end TunnellMap.FreeInvolution
