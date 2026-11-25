-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_quotEquiv_mk_e3a6de09a4c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:45.419823+00:00
-- url     : https://prove2.me/submissions/4b7db571-5b7e-4774-8bc5-e42d991cd3e1

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
theorem _root_.solution (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) (p : MvPolynomial σ F) :
    (quotEquiv g I h (Ideal.Quotient.mk I p) : Ω) = aeval g p :=
  rfl
end GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
