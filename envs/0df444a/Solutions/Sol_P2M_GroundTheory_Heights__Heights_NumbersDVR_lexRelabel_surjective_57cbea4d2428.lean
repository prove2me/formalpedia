-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_surjective_57cbea4d2428
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:21.091411+00:00
-- url     : https://prove2.me/submissions/f7a26d16-1bff-4aba-b9d3-9ef5fc8bd802

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
theorem _root_.solution (e : K ≃ Fin (Fintype.card K)) : Function.Surjective (lexRelabel e) :=
  fun i => ⟨fun k => ofLex i (e k), by
    change toLex (fun j => ofLex i (e (e.symm j))) = i
    simp only [Equiv.apply_symm_apply]
    rfl⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
