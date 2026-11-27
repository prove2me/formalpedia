-- Prove2me | solution 1 for Reformulated.TransposeInverseTheory.transposeInv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:18.53217+00:00
-- url     : https://prove2.me/submissions/019a8de5-18d0-4fcd-bdf5-77734f109bec

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.TransposeInverseTheory
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
namespace Reformulated.TransposeInverseTheory
theorem _root_.solution (g : GL n R) (i j : n) :
    (transposeInv g : GL n R) i j = (g⁻¹ : GL n R) j i := rfl
end Reformulated.TransposeInverseTheory
