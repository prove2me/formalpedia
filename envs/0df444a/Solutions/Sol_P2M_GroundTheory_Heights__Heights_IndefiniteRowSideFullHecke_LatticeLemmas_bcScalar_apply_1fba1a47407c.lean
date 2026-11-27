-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_bcScalar_apply_1fba1a47407c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:52.731664+00:00
-- url     : https://prove2.me/submissions/78a17809-4ef6-427f-a027-059cdd84f735

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [Field E] [NumberField E] [Algebra K E]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
theorem _root_.solution (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) :
    bcScalar K τ z b = ofComplex _ (τ (b : E) * (ofComplex τ).symm z) := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
