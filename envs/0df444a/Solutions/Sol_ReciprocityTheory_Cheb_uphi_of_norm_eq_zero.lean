-- Prove2me | solution 1 for ReciprocityTheory.Cheb.uphi_of_norm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:16.880492+00:00
-- url     : https://prove2.me/submissions/7e8ccaec-5d61-41dd-a1b1-b77b13ab4ea0

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {x : mixedSpace E} (hx : mixedEmbedding.norm x = 0) : uphi x = 0 := by
  unfold uphi
  rw [if_pos hx]
end ReciprocityTheory.Cheb
