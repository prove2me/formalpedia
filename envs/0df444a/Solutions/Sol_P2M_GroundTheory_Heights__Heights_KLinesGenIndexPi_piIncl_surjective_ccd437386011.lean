-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_piIncl_surjective_ccd437386011
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:37.224536+00:00
-- url     : https://prove2.me/submissions/024f7c76-fd15-457d-a965-bb767efd4632

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi

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
open GroundTheory.Heights₂.Heights.KLinesGenIndexPi
open AddSubgroup
variable {η : Type} {G : Type} [AddCommGroup G]
namespace GroundTheory.Heights₂.Heights.KLinesGenIndexPi
theorem _root_.solution (K : η → AddSubgroup G) : Function.Surjective (piIncl K) := by
  intro y
  refine ⟨fun i => ⟨(y : η → G) i, (AddSubgroup.mem_pi _).1 y.2 i (Set.mem_univ i)⟩, ?_⟩
  rfl
end GroundTheory.Heights₂.Heights.KLinesGenIndexPi
