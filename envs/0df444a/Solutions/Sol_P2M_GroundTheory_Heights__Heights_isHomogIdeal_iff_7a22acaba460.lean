-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:39.665783+00:00
-- url     : https://prove2.me/submissions/de4da1a3-e8ce-44b7-bece-dfdb9b428bf6

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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    have := h r hr i
    rwa [← decomposition.decompose'_apply] at this
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d
end GroundTheory.Heights₂.Heights
