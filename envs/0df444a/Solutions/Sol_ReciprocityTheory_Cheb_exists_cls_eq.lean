-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_cls_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:16.924948+00:00
-- url     : https://prove2.me/submissions/b093f7eb-bfbb-46d8-aeb1-eca8cd3c1028

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (C : ClassGroup (𝓞 E)) : ∃ b : NZIdeal E, cls b = C := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
  exact ⟨⟨I.1, nonZeroDivisors.ne_zero I.2⟩, hI⟩
end ReciprocityTheory.Cheb
