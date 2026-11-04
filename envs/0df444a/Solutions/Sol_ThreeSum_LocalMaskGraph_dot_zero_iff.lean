-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.dot_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:56.062071+00:00
-- url     : https://prove2.me/submissions/77f23312-2d88-40fd-984d-6ba33d23a2af

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_dot_bits

set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = 0 ↔ Disjoint s t := by
  rw [dot_bits,Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.symm
end ThreeSum.LocalMaskGraph
