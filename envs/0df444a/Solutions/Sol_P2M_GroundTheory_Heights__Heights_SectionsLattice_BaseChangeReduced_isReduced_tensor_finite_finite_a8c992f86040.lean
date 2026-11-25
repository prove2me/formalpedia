-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_finite_finite_a8c992f86040
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:11.307252+00:00
-- url     : https://prove2.me/submissions/1abec72c-90b0-4636-b2de-233cbb752434

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_PBaseChangeReduced

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
open TensorProduct
open GroundTheory.Heights₂.Heights.SectionsLattice
open GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
namespace GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
theorem _root_.solution {k : Type} [Field k] [CharZero k] (E E' : Type) [Field E]
    [Algebra k E] [Field E'] [Algebra k E'] [FiniteDimensional k E'] :
    IsReduced (E ⊗[k] E') := by
  have : Algebra.FormallyUnramified k E' := Algebra.FormallyUnramified.of_isSeparable k E'
  exact Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[k] E')
end GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
