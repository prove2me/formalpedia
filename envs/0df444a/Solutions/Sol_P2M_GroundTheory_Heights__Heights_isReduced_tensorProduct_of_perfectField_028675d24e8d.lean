-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_perfectField_028675d24e8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:33.941928+00:00
-- url     : https://prove2.me/submissions/8b4ec29d-a800-4c3d-8dbf-2be310ddb7e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_forall_field_83cd69f7ec3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_field_of_perfectField_9cfa4a0469a9

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
theorem _root_.solution (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (A : Type u) [CommRing A] [Algebra K A] [IsReduced A] :
    IsReduced (L ⊗[K] A) :=
  isReduced_tensorProduct_of_forall_field L
    (fun E _ _ _ => isReduced_tensorProduct_field_of_perfectField K L E) A
end GroundTheory.Heights₂.Heights
