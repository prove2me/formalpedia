-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_mem_primeAbove_933b8ede3481
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:30.048359+00:00
-- url     : https://prove2.me/submissions/7d38fb06-1273-4574-9a31-3ba86b59aafe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe

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
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
theorem _root_.solution [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    (q : Ideal (homLocRing P W)) (h : MRing ι R) :
    h ∈ primeAbove hPW hW hrel q ↔ h ∈ primeSet P W q := Iff.rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
