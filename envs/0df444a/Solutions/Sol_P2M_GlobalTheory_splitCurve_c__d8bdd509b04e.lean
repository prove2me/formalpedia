-- Prove2me | solution 1 for P2M_GlobalTheory_splitCurve_c__d8bdd509b04e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:32:35.385928+00:00
-- url     : https://prove2.me/submissions/9bd22968-2c25-4273-86c4-3ddaa7ceabd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution (A B : R) : (splitCurve A B).c₄ = 16 * (A ^ 2 - A * B + B ^ 2) := by
  simp only [splitCurve, c₄, b₂, b₄]; ring
end GlobalTheory
