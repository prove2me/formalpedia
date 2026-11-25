-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.TwistAlg.full_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:20.509785+00:00
-- url     : https://prove2.me/submissions/da63f6ed-f74d-4c7a-bc82-ccd727d87608

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_FullOfCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_pow_3db7e9c92ffa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman
universe u v w
namespace PositivityTheory.HtPt.KtwS
namespace TwistAlg
theorem _root_.solution : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twist, KThm.sub_pow, KThm.sub_pow, KThm.sub_pow, KThm.sub_twistMul M p m I hi,
    KThm.sub_twistMul M q m' I hi, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    KThm.span_zpow_pow I hi, KThm.span_zpow_pow I hi, KThm.span_zpow_pow I hi, mul_mul_mul_comm,
    ← pow_add, KThm.span_zpow_mul I hi]
  have e1 : p * (q * b₁ + b₂) = q * (p * b₁) + p * b₂ := by ring
  have e2 : m * ((q * b₁ + b₂ : ℕ) : ℤ) = m' * ((p * b₁ : ℕ) : ℤ) + m * (b₂ : ℤ) := by
    push_cast
    linear_combination (b₁ : ℤ) * h
  rw [e1, e2]
end TwistAlg
end PositivityTheory.HtPt.KtwS
