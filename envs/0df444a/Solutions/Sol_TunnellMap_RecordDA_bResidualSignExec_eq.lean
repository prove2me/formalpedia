-- Prove2me | solution 1 for TunnellMap.RecordDA.bResidualSignExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:28.081473+00:00
-- url     : https://prove2.me/submissions/a5d4ef9b-7320-4470-8e33-09af21467df3

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
attribute [local simp] TunnellMap.tripleLexLtExec_iff



set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (x : BResidual n) :
    bResidualSignExec x = bResidualSign x := by
  show _ = (bResidualInvolution n).signOf bResidualLexKey x
  have hneg : (bResidualInvolution n).neg x = negBResidual x := rfl
  unfold bResidualSignExec FreeInvolution.signOf bResidualLexKey
  rw [hneg]
  by_cases h : tripleLexLtExec x.1.1 (negBResidual x).1.1 = true
  · rw [if_pos h, if_pos ((tripleLexLtExec_iff _ _).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((tripleLexLtExec_iff _ _).mpr hc))]
end TunnellMap.RecordDA
