-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_toRingHom_apply_80ffa5b2f707
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:48.410412+00:00
-- url     : https://prove2.me/submissions/91343877-4fb6-44bc-a9ce-eb21795f78ae

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
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (a : A) :
    f.toRingHom a = f a :=
  rfl
end GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
