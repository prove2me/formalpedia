-- Prove2me | solution 1 for ThreeSum.MaskErase.natPositions_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:29.288985+00:00
-- url     : https://prove2.me/submissions/beff3499-1f7c-4623-be70-2f6cad1f9e1f

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase

set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    natPositions (s.erase a) = (natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a
end ThreeSum.MaskErase
