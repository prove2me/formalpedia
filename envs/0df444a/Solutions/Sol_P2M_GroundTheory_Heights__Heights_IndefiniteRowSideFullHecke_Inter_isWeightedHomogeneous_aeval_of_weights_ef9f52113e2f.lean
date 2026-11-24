-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:39.228039+00:00
-- url     : https://prove2.me/submissions/2d1dcf25-1f02-43dd-ba4d-56c4f2f14ef1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_weightedHomogeneousComponent_of_weights_c46b0d733486

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {w : σ → M} {ω : τ → M} {e : σ → MvPolynomial τ R}
    (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) {p : MvPolynomial σ R} {a : M}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous ω (aeval e p) a := by
  rw [← hp.weightedHomogeneousComponent_same, aeval_weightedHomogeneousComponent_of_weights w ω e he]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
