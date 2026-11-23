-- Prove2me | solution 1 for Reformulated.TransposeInverseTheory.transposeInv_transposeInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:10.668202+00:00
-- url     : https://prove2.me/submissions/c2564a19-c533-45dc-ab07-f6c1db2248b8

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
    transposeInv (transposeInv g) = g := transposeInvFun_involutive g
end Reformulated.TransposeInverseTheory
