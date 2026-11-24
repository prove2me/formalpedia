-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:08.558691+00:00
-- url     : https://prove2.me/submissions/a772f5e9-8f97-4389-80a8-f8261e428a45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
theorem _root_.solution (A : Finset (Fin n)) (b : Fin n) : Cech.sgn A b * Cech.sgn A b = 1 := by
  unfold Cech.sgn
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
