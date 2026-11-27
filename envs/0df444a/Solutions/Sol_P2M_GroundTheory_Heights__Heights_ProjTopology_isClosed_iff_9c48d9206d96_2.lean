-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ProjTopology_isClosed_iff_9c48d9206d96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:46.034487+00:00
-- url     : https://prove2.me/submissions/cc9e6359-d66d-4826-bb0b-1685db98d681

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ProjTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
open GroundTheory.Heights₂.Heights.ProjTopology
namespace GroundTheory.Heights₂.Heights.ProjTopology
theorem _root_.solution {s : Set (ℙ K V)} :
    IsClosed s ↔ IsClosed ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) :=
  isClosed_coinduced
end GroundTheory.Heights₂.Heights.ProjTopology
