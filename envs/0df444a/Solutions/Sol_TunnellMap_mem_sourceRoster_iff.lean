-- Prove2me | solution 1 for TunnellMap.mem_sourceRoster_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:30:15.235465+00:00
-- url     : https://prove2.me/submissions/4184cd16-31c5-42a1-9df8-f85286529ad1

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster

set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA
namespace TunnellMap
theorem _root_.solution (x : BResidual n) :
    x ∈ sourceRoster n ↔
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by
  constructor
  · exact fun hx => sourceRoster_canon x hx
  · intro hx
    rw [sourceRoster]
    refine List.mem_map.mpr ⟨(bResidualInvolution n).orbit x, ?_, hx⟩
    exact mem_residualSourceOrder _
end TunnellMap
