-- Prove2me | solution 2 for Reformulated.TransposeInverseTheory.coe_transposeInv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:54.950867+00:00
-- url     : https://prove2.me/submissions/bb523238-8605-4ae6-9b38-e43bf0823c77

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
theorem _root_.solution (g : GL n R) :
    (((transposeInv g)⁻¹ : GL n R) : Matrix n n R) = (g : Matrix n n R)ᵀ := rfl
end Reformulated.TransposeInverseTheory
