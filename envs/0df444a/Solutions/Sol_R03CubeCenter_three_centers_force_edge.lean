-- Prove2me | solution 1 for R03CubeCenter.three_centers_force_edge
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:20.349074+00:00
-- url     : https://prove2.me/submissions/832fc052-c647-445a-8f20-8a83ef8f97c1

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_ff1c84bf6a_R03CubeCenter_v1

/- Candidate-only finite cube-center obstruction and scalar bookkeeping.
   The arbitrary-graph factor projector and cycle/fiber identity are not
   formalized in this source. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 100000
namespace R03CubeCenter

end R03CubeCenter

open R03CubeCenter
theorem solution : ∀ m : Fin 128,
    cardinality m=3 → 2≤portCount m → Dominating m → HasCenterEdge m := by
  unfold cardinality portCount Dominating HasCenterEdge bit chosen adjacent
  decide +kernel
