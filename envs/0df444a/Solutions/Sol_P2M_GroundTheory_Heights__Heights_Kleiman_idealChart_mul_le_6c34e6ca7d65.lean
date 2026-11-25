-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_mul_le_6c34e6ca7d65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:49.241868+00:00
-- url     : https://prove2.me/submissions/e586c717-95de-452a-af44-fd53b5ce2056

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mul_le_ff09cd164858

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
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealChart J I * idealChart J' I ≤ idealChart (x := x) (J * J') I :=
  Ideal.mul_le.mpr fun a ha b hb => by
    have := idealMod_mul_le (x := x) J J' I (Submodule.mul_mem_mul ha hb)
    simpa using this
end GroundTheory.Heights₂.Heights.Kleiman
