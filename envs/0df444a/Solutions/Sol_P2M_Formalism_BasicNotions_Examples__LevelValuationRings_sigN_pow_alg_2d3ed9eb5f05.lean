-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_pow_alg_2d3ed9eb5f05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:04.158875+00:00
-- url     : https://prove2.me/submissions/20d0b024-850a-40be-a59f-7acb1093105d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272
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
theorem _root_.solution (k : ℕ) (x : Wn p n) :
    (sigN p n ^ k) (algebraMap (Wn p n) (Qn p n) x) =
      algebraMap (Wn p n) (Qn p n) ((WittVector.frobenius^[k]) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    show sigN p n ((sigN p n ^ k) _) = _
    rw [ih, sigN_alg]
end Formalism.BasicNotions.Examples₂.LevelValuationRings
