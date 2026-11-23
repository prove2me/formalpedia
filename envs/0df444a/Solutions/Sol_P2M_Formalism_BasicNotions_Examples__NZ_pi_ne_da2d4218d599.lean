-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:23.392646+00:00
-- url     : https://prove2.me/submissions/fc43dc6e-d0ff-480b-be74-590788d8d479

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
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
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hϖ.ne_zero
end Formalism.BasicNotions.Examples₂.NZ
