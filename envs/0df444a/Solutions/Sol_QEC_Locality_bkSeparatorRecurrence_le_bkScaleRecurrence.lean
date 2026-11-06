-- Prove2me | solution 1 for QEC.Locality.bkSeparatorRecurrence_le_bkScaleRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:25:55.843093+00:00
-- url     : https://prove2.me/submissions/2a8b1f38-cb0f-4dfc-b907-ebf5be66ead0

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_bkScaleRecurrence_mono
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkScaleRecurrence_card

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) (r : Nat)
    (hcard : vertices.card ≤ r) :
    bkSeparatorRecurrence G d vertices ≤ bkScaleRecurrence G d r :=
  (bkSeparatorRecurrence_le_bkScaleRecurrence_card G d vertices).trans
    (bkScaleRecurrence_mono G d hcard)
end QEC.Locality
