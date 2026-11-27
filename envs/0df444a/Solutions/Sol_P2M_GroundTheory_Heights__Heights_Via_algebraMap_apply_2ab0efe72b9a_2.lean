-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_Via_algebraMap_apply_2ab0efe72b9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:12:21.474532+00:00
-- url     : https://prove2.me/submissions/6ffb9660-45fc-47f0-8f5c-2ad223cff3c5

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
open GroundTheory.Heights₂.Heights.Via
variable {R : Type*} [CommRing R] (φ : R →+* ℂ)
namespace GroundTheory.Heights₂.Heights.Via
theorem _root_.solution (r : R) : algebraMap R (Via φ) r = ofComplex φ (φ r) := rfl
end GroundTheory.Heights₂.Heights.Via
