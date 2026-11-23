-- Prove2me | solution 1 for Reformulated.TransposeInverseTheory.coe_transposeInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:08.609687+00:00
-- url     : https://prove2.me/submissions/cdc18b43-5ab0-40d9-85af-2615c6a739e7

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
    ((transposeInv g : GL n R) : Matrix n n R) = ((g⁻¹ : GL n R) : Matrix n n R)ᵀ := rfl
end Reformulated.TransposeInverseTheory
