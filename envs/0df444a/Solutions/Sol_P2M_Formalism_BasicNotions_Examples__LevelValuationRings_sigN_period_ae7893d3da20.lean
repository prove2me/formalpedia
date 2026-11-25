-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_period_ae7893d3da20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:57.634903+00:00
-- url     : https://prove2.me/submissions/8ee057d5-b979-44c1-8256-669de535af58

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_frob_iter_a51111b6d48b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_pow_alg_2d3ed9eb5f05
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G QuadraticAlgebra
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.LevelValuationRings
theorem _root_.solution (hn : n ≠ 0) : sigN p n ^ n = 1 := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Wn p n))
  ext1 x
  show (sigN p n ^ n) (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) x
  rw [sigN_pow_alg, frob_iter p n hn]
end Formalism.BasicNotions.Examples₂.LevelValuationRings
