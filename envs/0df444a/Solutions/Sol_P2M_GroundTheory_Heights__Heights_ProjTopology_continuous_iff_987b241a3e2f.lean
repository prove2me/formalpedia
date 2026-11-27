-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjTopology_continuous_iff_987b241a3e2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:44.664645+00:00
-- url     : https://prove2.me/submissions/a4c1f099-2d22-4b03-aa77-e095ec22d681

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
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {g : ℙ K V → Y} :
    Continuous g ↔ Continuous (g ∘ Projectivization.mk' K) :=
  continuous_coinduced_dom
end GroundTheory.Heights₂.Heights.ProjTopology
