-- Prove2me | solution 1 for TunnellMap.RecordDA.terminalRunExec_queue_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:32:05.771238+00:00
-- url     : https://prove2.me/submissions/f752f4f8-c9e1-4527-9ead-1c9152c6c755

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_terminalRunExec_eq

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (terminalRunExec frames).queue = [] := by
  rw [terminalRunExec_eq]
  exact terminalRun_queue_nil hn hnpos frames hcard
end TunnellMap.RecordDA
