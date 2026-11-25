-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_incl_apply_32db40748d5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:16.898906+00:00
-- url     : https://prove2.me/submissions/a1b2aa20-8817-4aad-b129-2e66b81b9e42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFnDegAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}
namespace GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
theorem _root_.solution {S T : Subalgebra F Ω} (h : S ≤ T) (x : S) :
    ((Subalgebra.inclusion h).toRingHom x : Ω) = x :=
  rfl
end GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
