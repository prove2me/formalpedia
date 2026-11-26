-- Prove2me | solution 1 for TunnellMap.FreeInvolution.orbit_canonicalRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:13.703158+00:00
-- url     : https://prove2.me/submissions/0e149e14-bdbf-4133-b13e-4b015e83d7e9

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_Antipodal
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift



set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]
namespace TunnellMap.FreeInvolution
theorem _root_.solution (key : X → K)
    (hkey : Function.Injective key) (q : I.Orbit) :
    I.orbit (I.canonicalRepresentative key hkey q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
      change I.orbit (I.canonicalPoint key x) = I.orbit x
      unfold canonicalPoint
      split <;> simp [I.orbit_neg]
end TunnellMap.FreeInvolution
