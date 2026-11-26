-- Prove2me | solution 1 for TunnellMap.targetLiftSign_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:46.765273+00:00
-- url     : https://prove2.me/submissions/8d549a76-66dc-4798-b3c3-bd642516e393

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (v : Triple) :
    targetLiftSign v = 1 ∨ targetLiftSign v = -1 := by
  unfold targetLiftSign
  split
  · exact Or.inl rfl
  · exact Or.inr rfl
end TunnellMap
