-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_right_3ac668c7eb0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:02.769379+00:00
-- url     : https://prove2.me/submissions/c1210dcc-be4b-4858-95de-f5ae80cd3719

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
    (w : l ⊕ l → R) : symplOmega w (0 : l ⊕ l → R) = 0 := by
  simp [symplOmega]
end GroundTheory.Heights₂.Heights.PSymplExtMem
