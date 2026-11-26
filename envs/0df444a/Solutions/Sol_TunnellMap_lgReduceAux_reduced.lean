-- Prove2me | solution 1 for TunnellMap.lgReduceAux_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:32.902116+00:00
-- url     : https://prove2.me/submissions/9e997bfa-6fc0-4943-ba4f-18fda28b28a6

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_lgNext_bound

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution (u v : Triple) : IsReducedPair (lgReduceAux u v) := by
  induction u, v using lgReduceAux.induct with
  | case1 u v h ih =>
      rw [lgReduceAux, dif_pos h]
      exact ih
  | case2 u v h =>
      rw [lgReduceAux, dif_neg h]
      exact ⟨lgNext_bound u v, not_lt.mp h⟩
end TunnellMap
