-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:36.561189+00:00
-- url     : https://prove2.me/submissions/78ec1e19-4ae7-4f05-a49a-36ecace064cb

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
theorem _root_.solution {q : Ideal (homLocRing P W)} {s : K → ℕ} {f g : MRing ι R}
    (hf : IsMultiHomog f s) (hg : IsMultiHomog g s) (hgW : g ∉ W) (h : f ∈ primeSet P W q) :
    ValIn P W q (frac P f / frac P g) := by
  have := h s g hg hgW
  rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
