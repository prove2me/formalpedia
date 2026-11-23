-- Prove2me | solution 1 for P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:03.661321+00:00
-- url     : https://prove2.me/submissions/e5ed8643-c1a4-41fd-8191-f8cc4c0a67a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.OrbitGrowth
theorem _root_.solution (a b : Module.End ℂ M) (y : M) : (a * b) y = a (b y) := rfl
end GlobalTheory.OrbitGrowth
