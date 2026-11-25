-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_stalkEquiv_apply_215b710176b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:06.669356+00:00
-- url     : https://prove2.me/submissions/21364b84-3de3-44a6-9a11-76d1e838e106

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {X : Scheme.{u}} (L : X.Modules)
variable {L}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (r : locRing X p) :
    stalkEquiv hp he r = r • germM hp e := rfl
end GroundTheory.Heights₂.Heights
