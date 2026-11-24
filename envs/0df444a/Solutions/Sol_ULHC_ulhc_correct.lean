-- Prove2me | solution 1 for ULHC.ulhc_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:51:06.845213+00:00
-- url     : https://prove2.me/submissions/26d1d6c6-0912-4ca4-923f-f0dc0660b9b6

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_pathComplete
import Theorems.Thm_ULHC_ulhc_complete
import Theorems.Thm_ULHC_ulhc_sound


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} (hs : Solid V) :
    ulhc V = true ↔ ∃ H, Deg2 V H ∧ ncomp V H = 1 := by
  constructor
  · exact ulhc_sound
  · rintro ⟨H, hH, hHam⟩
    exact ulhc_complete hs hH hHam (pathComplete hs hH hHam)
end ULHC
