-- Prove2me | solution 1 for TunnellMap.tau_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:34.473829+00:00
-- url     : https://prove2.me/submissions/b9eee066-b461-40da-9a4c-4f8ed330d28e

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_TauLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution : Function.Injective tau := by
  intro d e h
  simpa using congrArg tauInv h
end TunnellMap
