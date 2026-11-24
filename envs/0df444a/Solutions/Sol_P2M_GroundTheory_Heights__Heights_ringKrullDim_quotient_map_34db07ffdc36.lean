-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:57.822797+00:00
-- url     : https://prove2.me/submissions/186fcf75-9a2d-4151-a560-3c68019bdc74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal A) :
    ringKrullDim (A' ⧸ V.map σ) = ringKrullDim (A ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V (V.map σ) σ rfl)).symm
end GroundTheory.Heights₂.Heights
