-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_map__27b43c6efe6a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:14.006522+00:00
-- url     : https://prove2.me/submissions/ed36be0e-1c80-475b-9413-0d6a251d2d4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {R : Type*} [CommRing R]
variable {k n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace IsWeightedHomogeneous
theorem _root_.solution {σ S : Type*} [CommSemiring S] {w : σ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : R →+* S) :
    IsWeightedHomogeneous w (MvPolynomial.map φ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])
end IsWeightedHomogeneous
end GroundTheory.Heights₂.Heights
