-- Prove2me | solution 1 for TunnellMap.BlockGen.oneBlock_storage_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:26:17.493146+00:00
-- url     : https://prove2.me/submissions/e15d6062-eb5d-4e3e-bb55-74703dbc6a76

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState

set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (hst : OneBlock s F st) :
    st.pending.length ≤ (blockIndexList n F (st.nextBlock - 1)).length := by
  refine le_trans (List.IsSuffix.length_le hst) ?_
  rw [blockRecords, List.length_mergeSort]
  exact List.length_filterMap_le _ _
end TunnellMap.BlockGen
