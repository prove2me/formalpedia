-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:28:22.22378+00:00
-- url     : https://prove2.me/submissions/cf76aa45-a547-4065-8be9-440ddc1dde80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9

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
theorem _root_.solution (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) :
    (twistMul M p m).sub I = (twistSys S x m).sub I * M.sub I ^ p := by
  rw [twistMul, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub]
end GroundTheory.Heights₂.Heights.Kleiman
