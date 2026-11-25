-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:27:38.372482+00:00
-- url     : https://prove2.me/submissions/ca99dfab-a78d-48fb-b31a-0c080c8d87d4

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
open GroundTheory.Heights₂.Heights.Kleiman.LineBundle
namespace GroundTheory.Heights₂.Heights.Kleiman.LineBundle
theorem _root_.solution (Q : LineBundle S x) (n : ℕ) :
    (Q.powBundle n).toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Q.powBundle n).toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [ih]
end GroundTheory.Heights₂.Heights.Kleiman.LineBundle
