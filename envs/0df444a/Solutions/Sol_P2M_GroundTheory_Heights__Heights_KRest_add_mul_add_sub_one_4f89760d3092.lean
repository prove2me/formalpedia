-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_add_mul_add_sub_one_4f89760d3092
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:10.487802+00:00
-- url     : https://prove2.me/submissions/bd828d3e-cbdf-4818-bdbb-142a7a18209e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRestHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.KRest
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution (r a : ℕ) :
    (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by
  rcases r with _ | r
  · simp
  rcases a with _ | a
  · simp
  have h1 : r + 1 + (a + 1) - 1 = r + a + 1 := by omega
  rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring
end GroundTheory.Heights₂.Heights.KRest
