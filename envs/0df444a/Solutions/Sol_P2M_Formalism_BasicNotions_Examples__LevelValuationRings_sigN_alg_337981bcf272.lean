-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.081962+00:00
-- url     : https://prove2.me/submissions/b54c4ff5-7d6f-4eae-8733-9f5fbca47324

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
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
theorem _root_.solution (x : Wn p n) :
    sigN p n (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) (WittVector.frobenius x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
end Formalism.BasicNotions.Examples₂.LevelValuationRings
