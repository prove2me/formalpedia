-- Prove2me | solution 1 for P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:48.06933+00:00
-- url     : https://prove2.me/submissions/a8b1cd7a-99e2-4ee7-9532-2bfe82748eed

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {a : Type} [DecidableEq a] : (1 : Matrix a a E).map c = 1 := by
  exact Matrix.map_one c (map_zero c) (map_one c)
end PositivityTheory.ThK.SiegelT
