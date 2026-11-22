-- Prove2me | solution 1 for P2M_GlobalTheory_splitCurve___21d0522b5d77
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:53.948127+00:00
-- url     : https://prove2.me/submissions/ba7d5872-6285-400b-a0f1-448c01a4412e

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
theorem _root_.solution (A B : R) : (splitCurve A B).Δ = 16 * A ^ 2 * B ^ 2 * (A - B) ^ 2 := by
  simp only [splitCurve, Δ, b₂, b₄, b₆, b₈]; ring
end GlobalTheory
