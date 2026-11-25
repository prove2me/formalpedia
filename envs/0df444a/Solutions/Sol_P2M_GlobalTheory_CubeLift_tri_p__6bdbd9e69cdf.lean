-- Prove2me | solution 1 for P2M_GlobalTheory_CubeLift_tri_p__6bdbd9e69cdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:51.929697+00:00
-- url     : https://prove2.me/submissions/87687808-c216-413a-b26b-2e06d6cc7841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (a b c : X →+ Y) : (tri a b c).comp p₁ = a := by ext; simp
end GlobalTheory.CubeLift
