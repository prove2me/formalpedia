-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.parented_base_in_rootComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:31:59.998822+00:00
-- url     : https://prove2.me/submissions/7a7be733-fb8b-4de8-be6e-3fd7a2921c51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff_parented_base
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_parented_base_root_path
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_rootComponent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (v : GraphVertex S 2)
    (hv : v ∈ baseMarks S n sigma) (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    physicalNode S n 0 v ∈ rootComponent S n sigma := by
  exact (mem_rootComponent S n sigma _).mpr
    ⟨(root_marked_iff_parented_base S n sigma).mpr ⟨v, hv, u, hp⟩,
      (mem_marks_physical S n sigma 0 v).mpr hv,
      parented_base_root_path S n sigma v hv u hp⟩
end QEC.Coding.BDL26CanonicalHistoryMarks
