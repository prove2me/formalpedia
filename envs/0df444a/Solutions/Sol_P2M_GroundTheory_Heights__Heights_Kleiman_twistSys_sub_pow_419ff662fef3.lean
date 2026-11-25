-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_pow_419ff662fef3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:27.309651+00:00
-- url     : https://prove2.me/submissions/970fff29-b039-486c-9bff-b53c717054e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistSys_9d375c81eb90

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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (n : ℕ) (I : Chart x) :
    (twistSys S x c).sub I ^ n = (twistSys S x (n * c)).sub I := by
  rw [← SubSystem.pow_sub, pow_twistSys]
end GroundTheory.Heights₂.Heights.Kleiman
