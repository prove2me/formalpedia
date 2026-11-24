-- Prove2me | solution 1 for P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:11.054958+00:00
-- url     : https://prove2.me/submissions/70304e8b-380b-4fa9-96ba-1e1b4b688372

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
theorem _root_.solution {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : (A * B).map c = A.map c * B.map c := by
  exact Matrix.map_mul (f := c.toRingHom)
end PositivityTheory.ThK.SiegelT
