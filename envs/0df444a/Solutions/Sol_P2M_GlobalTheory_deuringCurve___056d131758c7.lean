-- Prove2me | solution 1 for P2M_GlobalTheory_deuringCurve___056d131758c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:51.848875+00:00
-- url     : https://prove2.me/submissions/5be0d8db-f240-4290-856b-c42647cef08d

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
theorem _root_.solution (a b : R) : (deuringCurve a b).Δ = b ^ 3 * (a ^ 3 - 27 * b) := by
  simp only [deuringCurve, Δ, b₂, b₄, b₆, b₈]; ring
end GlobalTheory
