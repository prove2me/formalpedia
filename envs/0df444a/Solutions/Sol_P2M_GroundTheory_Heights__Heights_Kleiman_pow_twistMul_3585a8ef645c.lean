-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:23.55648+00:00
-- url     : https://prove2.me/submissions/96869091-550e-47a8-a4aa-e08673d56799

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146

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
theorem _root_.solution (M : SubSystem S x Ω) (q j : ℕ) (m : ℤ) :
    (twistMul M q m).pow j = twistMul M (j * q) (j * m) := by
  have h := twistMul_twistMul M q j m 0
  rw [add_zero] at h
  rw [← h]
  exact (SubSystem.twist_twistSys_zero _).symm
end GroundTheory.Heights₂.Heights.Kleiman
