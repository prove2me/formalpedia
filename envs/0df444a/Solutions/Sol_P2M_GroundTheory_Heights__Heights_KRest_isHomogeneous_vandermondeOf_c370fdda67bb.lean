-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_isHomogeneous_vandermondeOf_c370fdda67bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:27.107799+00:00
-- url     : https://prove2.me/submissions/4a9def3f-f1f3-46be-9996-eb2924dfaf9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRestHom

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.KRest
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution {σ R : Type*} [CommRing R] {m : ℕ}
    (v : Fin m → MvPolynomial σ R) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (RestTerms.vandermondeOf v).IsHomogeneous (∑ i : Fin m, (Finset.Ioi i).card) := by
  unfold RestTerms.vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  have h := IsHomogeneous.prod (Finset.Ioi i) (fun j => v i - v j) (fun _ => 1)
    fun j _ => (hv i).sub (hv j)
  simpa using h
end GroundTheory.Heights₂.Heights.KRest
