-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_decompose_blockWeight_8e63e41e72c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:43.376619+00:00
-- url     : https://prove2.me/submissions/9fc1c06c-0173-4cce-9eb3-d303c389474f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (r : MRing ι R) (b : K → ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) r b : MRing ι R) =
      weightedHomogeneousComponent (blockWeight ι) b r :=
  weightedDecomposition.decompose'_apply R (blockWeight ι) r b
end GroundTheory.Heights₂.Heights.NumbersDVR
