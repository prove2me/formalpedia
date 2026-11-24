-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:15.849271+00:00
-- url     : https://prove2.me/submissions/fbea1049-b6e3-41a9-9706-4421a681b7ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog

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
variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (e : K ≃ Fin (Fintype.card K)) : Function.Injective (lexRelabel e) := by
  intro a b h
  have h' : (fun j => a (e.symm j)) = fun j => b (e.symm j) := toLex.injective h
  funext k
  simpa using congrFun h' (e k)
end GroundTheory.Heights₂.Heights.NumbersDVR
