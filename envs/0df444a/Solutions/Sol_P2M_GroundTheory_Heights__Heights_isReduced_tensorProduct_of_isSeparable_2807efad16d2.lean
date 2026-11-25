-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_isSeparable_2807efad16d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:23.232857+00:00
-- url     : https://prove2.me/submissions/59ce98d8-c80b-46aa-bbf2-01d0606c7b30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_forall_field_83cd69f7ec3b

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
open TensorProduct
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [Algebra.EssFiniteType F E]
    (D : Type u) [CommRing D] [Algebra F D] [IsReduced D] : IsReduced (E ⊗[F] D) := by
  refine isReduced_tensorProduct_of_forall_field E (fun M _ _ _ => ?_) D
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  have : IsReduced (M ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm F E M).toAlgHom (AlgEquiv.injective _)
end GroundTheory.Heights₂.Heights
