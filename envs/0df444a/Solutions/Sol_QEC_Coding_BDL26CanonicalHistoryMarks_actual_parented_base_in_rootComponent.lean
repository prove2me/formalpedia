-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.actual_parented_base_in_rootComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:28:41.407197+00:00
-- url     : https://prove2.me/submissions/8b2a78cf-9654-40bf-819a-f082a4373f0a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_parented_base_in_rootComponent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (j : Nat) (s : Input S (2 * j))
    (v : GraphVertex S 2) (hv : physicalNode S (2 * j) 0 v ∈ actualMarks S j s)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    physicalNode S (2 * j) 0 v ∈ actualRootComponent S j s :=
  parented_base_in_rootComponent S (2 * j) s v
    ((mem_marks_physical S (2 * j) s 0 v).mp hv) u hp
end QEC.Coding.BDL26CanonicalHistoryMarks
