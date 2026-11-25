-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_pow_le_520c32532769
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:24.646608+00:00
-- url     : https://prove2.me/submissions/6b5b967c-159d-4bd6-8757-d9d44d1b2e6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_mul_le_6c34e6ca7d65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_top_77cd259be07e

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
theorem _root_.solution (P : Ideal (Poly k N)) (I : Chart x) (n : ℕ) :
    idealChart P I ^ n ≤ idealChart (x := x) (P ^ n) I := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, idealChart_top, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left ih).trans (idealChart_mul_le _ _ I)
end GroundTheory.Heights₂.Heights.Kleiman
