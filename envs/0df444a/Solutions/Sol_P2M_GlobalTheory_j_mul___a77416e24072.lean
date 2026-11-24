-- Prove2me | solution 1 for P2M_GlobalTheory_j_mul___a77416e24072
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:42:56.197564+00:00
-- url     : https://prove2.me/submissions/5041e26e-69b9-4509-8542-4b9abb75eb5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← coe_Δ', mul_right_comm, Units.inv_mul, one_mul]
end GlobalTheory
