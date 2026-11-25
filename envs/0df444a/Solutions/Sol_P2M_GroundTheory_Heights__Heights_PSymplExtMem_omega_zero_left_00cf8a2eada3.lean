-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_left_00cf8a2eada3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:01.429325+00:00
-- url     : https://prove2.me/submissions/cf1ec584-9b6d-4805-ae98-660c084fc503

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplExtMem

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplExtMem
namespace GroundTheory.Heights₂.Heights.PSymplExtMem
theorem _root_.solution {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega (0 : l ⊕ l → R) w = 0 := by
  simp [symplOmega]
end GroundTheory.Heights₂.Heights.PSymplExtMem
