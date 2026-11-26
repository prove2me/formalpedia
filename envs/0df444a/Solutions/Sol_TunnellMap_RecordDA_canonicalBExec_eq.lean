-- Prove2me | solution 1 for TunnellMap.RecordDA.canonicalBExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:21.230487+00:00
-- url     : https://prove2.me/submissions/c343710b-069c-4a5d-825a-8b358c39207b

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
    canonicalBExec x =
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) := by
  show _ = (bResidualInvolution n).canonicalPoint bResidualLexKey x
  have hneg : (bResidualInvolution n).neg x = negBResidual x := rfl
  unfold canonicalBExec FreeInvolution.canonicalPoint bResidualLexKey
  rw [hneg]
  by_cases h : tripleLexLtExec x.1.1 (negBResidual x).1.1 = true
  · rw [if_pos h, if_pos ((tripleLexLtExec_iff _ _).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((tripleLexLtExec_iff _ _).mpr hc))]
end TunnellMap.RecordDA
