-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:10.851836+00:00
-- url     : https://prove2.me/submissions/1afd0f58-e71a-4378-bfd2-e79994a286ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetIndepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
namespace ReciprocityTheory.ChartRestriction.G.AR
theorem _root_.solution {D a : ℕ} {α : Fin D → ℕ} : α ∈ multiLt D a ↔ ∑ k, α k < a := by
  simp [multiLt, Finset.mem_biUnion, Finset.Nat.mem_antidiagonalTuple]
end ReciprocityTheory.ChartRestriction.G.AR
