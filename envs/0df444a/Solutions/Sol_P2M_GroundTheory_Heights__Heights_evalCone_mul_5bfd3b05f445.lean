-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:14.211938+00:00
-- url     : https://prove2.me/submissions/30b474b4-62bc-46d3-9ff1-d06c3c57da32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [CommRing F] (z : Cone n F) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := eval₂_mul _ _
end GroundTheory.Heights₂.Heights
