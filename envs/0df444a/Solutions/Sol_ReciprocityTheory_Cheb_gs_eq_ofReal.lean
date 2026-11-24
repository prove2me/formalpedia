-- Prove2me | solution 1 for ReciprocityTheory.Cheb.gs_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.320979+00:00
-- url     : https://prove2.me/submissions/6d0a7ae8-c672-4146-803e-f35a219c81e7

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe

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
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * (mixedEmbedding.norm x) ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x)]
  push_cast; ring
end ReciprocityTheory.Cheb
