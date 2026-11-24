-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_embZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:52.391568+00:00
-- url     : https://prove2.me/submissions/6f7ddd5c-2796-4294-bd3a-259120a3080d

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Theorems.Thm_ReciprocityTheory_Cheb_embZ_apply

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
theorem _root_.solution (α : 𝓞 E) : mixedEmbedding.norm (embZ α) = |((Algebra.norm ℤ α : ℤ) : ℝ)| := by
  rw [embZ_apply, norm_eq_norm, ← Algebra.coe_norm_int]
  push_cast
  rfl
end ReciprocityTheory.Cheb
