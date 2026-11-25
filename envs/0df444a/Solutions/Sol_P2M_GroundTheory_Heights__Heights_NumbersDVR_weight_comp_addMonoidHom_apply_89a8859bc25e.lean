-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_apply_89a8859bc25e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:51.44808+00:00
-- url     : https://prove2.me/submissions/2a831634-3c4a-4d8b-8daf-52d699db577e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel

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
variable {σ : Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M)
    (f : M →+ M') (d : σ →₀ ℕ) : Finsupp.weight (fun v => f (w v)) d = f (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]
end GroundTheory.Heights₂.Heights.NumbersDVR
