-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_embZ_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:16.328685+00:00
-- url     : https://prove2.me/submissions/72bdf719-2171-4bec-b154-379d50b2e8c6

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Theorems.Thm_ReciprocityTheory_Cheb_norm_embZ


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
theorem _root_.solution {g : 𝓞 E} (hg : g ≠ 0) : mixedEmbedding.norm (embZ g) ≠ 0 := by
  rw [norm_embZ]
  have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
  exact abs_ne_zero.2 (Int.cast_ne_zero.2 this)
end ReciprocityTheory.Cheb
