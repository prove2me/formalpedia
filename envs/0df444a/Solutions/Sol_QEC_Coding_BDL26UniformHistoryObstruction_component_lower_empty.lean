-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.component_lower_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:20:24.858124+00:00
-- url     : https://prove2.me/submissions/19bd802c-0d15-488d-aae6-c8e329839df8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_singleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : lowerRegion S j (component S j lower p hp) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have he := (Finset.mem_filter.mp hq).2
  rw [component_singleton] at he
  have hv := congrArg (fun w : UniformNode S j => w.1.val) (Finset.mem_singleton.mp he)
  change 2 * j + 3 = 2 * j + 4 at hv
  omega
end QEC.Coding.BDL26UniformHistoryObstruction
