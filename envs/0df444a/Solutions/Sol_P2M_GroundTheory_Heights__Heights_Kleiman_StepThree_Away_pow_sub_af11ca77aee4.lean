-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_pow_sub_af11ca77aee4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:49.769249+00:00
-- url     : https://prove2.me/submissions/ab273633-1381-4726-9855-e22205c4f194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twist_sub_46528efab20e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_zero_b9603c922eb1

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
theorem _root_.solution (Q : SubSystem S x Ω) (I : Chart x) (n : ℕ) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => exact (twistMod_zero I).trans (pow_zero _).symm
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub, ih, pow_succ']
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
