-- Prove2me | solution 1 for P2M_GlobalTheory_deuringCurve_c__6d8748b3be6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:18.165312+00:00
-- url     : https://prove2.me/submissions/00e5ad90-95cc-4454-9807-32de010334a9

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
theorem _root_.solution (a b : R) : (deuringCurve a b).c₄ = a * (a ^ 3 - 24 * b) := by
  simp only [deuringCurve, c₄, b₂, b₄]; ring
end GlobalTheory
