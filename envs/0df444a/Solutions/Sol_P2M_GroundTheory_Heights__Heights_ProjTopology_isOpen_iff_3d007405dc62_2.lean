-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ProjTopology_isOpen_iff_3d007405dc62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:50.016476+00:00
-- url     : https://prove2.me/submissions/e92a403f-527b-4a76-b0dc-45b1dd435081

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
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) :=
  isOpen_coinduced
end GroundTheory.Heights₂.Heights.ProjTopology
