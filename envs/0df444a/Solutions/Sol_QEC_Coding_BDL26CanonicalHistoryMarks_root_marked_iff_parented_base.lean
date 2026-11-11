-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.root_marked_iff_parented_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:12:59.460742+00:00
-- url     : https://prove2.me/submissions/2a44d409-c196-495c-a41c-bf9d07c4ba98

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_oneMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution : root S n ∈ marks S n sigma ↔
    ∃ v ∈ baseMarks S n sigma, ∃ u, parent S 1 v = some u := by
  rw [root_marked_iff]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv, hp⟩ := (mem_oneMarks S n sigma u).mp hu
    exact ⟨v, hv, u, hp⟩
  · rintro ⟨v, hv, u, hp⟩
    exact ⟨u, (mem_oneMarks S n sigma u).mpr ⟨v, hv, hp⟩⟩
end QEC.Coding.BDL26CanonicalHistoryMarks
