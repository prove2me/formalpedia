-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_lower_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:30:43.761376+00:00
-- url     : https://prove2.me/submissions/ec4cddfd-d380-43ad-ab1e-1cad93b3e04e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_componentWithLower_singleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    lowerOwnerMaskRegion (componentWithLower lower p hp) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have he := (Finset.mem_filter.mp hq).2
  rw [componentWithLower_singleton] at he
  have hv := congrArg (fun w : BDL26TopOwnerIsolation.Node => w.1.val)
    (Finset.mem_singleton.mp he)
  norm_num [BDL26TopOwnerIsolation.topNode] at hv
end QEC.Coding.BDL26OwnerIncidenceMasks
