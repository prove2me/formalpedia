-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:04.266478+00:00
-- url     : https://prove2.me/submissions/1f4f10d7-bdd9-401e-9c24-3ce0798bf065

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem
namespace GroundTheory.Heights₂.Heights.Kleiman.SubSystem
theorem _root_.solution (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I = _
    rw [twistMod_eq_span 0 I hi, zpow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub_eq_mul_of_line, ih, pow_succ']
end GroundTheory.Heights₂.Heights.Kleiman.SubSystem
