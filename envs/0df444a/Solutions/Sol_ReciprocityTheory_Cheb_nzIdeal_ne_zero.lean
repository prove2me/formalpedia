-- Prove2me | solution 1 for ReciprocityTheory.Cheb.nzIdeal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.595657+00:00
-- url     : https://prove2.me/submissions/d65163b8-adaa-4280-96a2-064932b9e907

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat

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
theorem _root_.solution (a : NZIdeal E) : a.1 ≠ 0 := by
  intro h; exact a.2 (by rw [h]; rfl)
end ReciprocityTheory.Cheb
