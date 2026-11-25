-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_quotient_5d81cc5f85b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:21.32788+00:00
-- url     : https://prove2.me/submissions/45cc06cf-82cb-4bba-b0b8-4d994323ca33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_integers_770829070650

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (I : Ideal (𝓞 K)) :
    Nat.card (𝓞 L ⊗[𝓞 K] (𝓞 K ⧸ I)) = Nat.card (𝓞 K ⧸ I) ^ Module.finrank K L := by
  rw [← Nat.card_congr (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (𝓞 L) I).toEquiv,
    ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    ← Ideal.absNorm_apply, Ideal.absNorm_algebraMap, finrank_integers]
end GroundTheory.Heights₂.Heights.LatticeLemmas
